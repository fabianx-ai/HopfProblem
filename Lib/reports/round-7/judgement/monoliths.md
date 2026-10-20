# Judgement packet: files over 1,800 lines to split by topic

Cut each file along the topics the auditors list; every new file is a Mathlib-style module with its own docstring; nothing deleted; envdiff shows module moves only (0 lost, 0 changed types).

## Lib/AlgebraicTopology/FundamentalGroup/VanKampen.lean  (165 declarations, 1823 lines)
verdict: C (project residue in the mathematics: a superseded monolith duplicating `VanKampen/{Basic,PathValue,Pushout,Surjectivity}.lean`, tied to project namespaces)
twin: Hatcher Thm 1.20 (named in docstring l.15–16, including the uniqueness half); no Mathlib twin (PR #28246 pending)
findings:
- l.47–1770: the same `LocalPathValue`, `PathValue`, `TwoOpenCover`, `pathIn`, `localValue`, `extension`, `rectangleBoundaryHomotopy`, `lift`, `pushoutEquiv`, `inclusionHomU_surjective_of_overlapHomV_surjective` as the split files, under `FundamentalGroup.VanKampen.` instead of `FundamentalGroup.VanKampen.Cocone.` — two complete copies of the van Kampen development live in `Lib` (this one 1823 lines, the split one 2221 lines)
- l.447–478 the uniqueness argument calls `TriangleRegularBaseFundamentalGroup.basedLoop` (the project's `Threefold`-computation namespace, imported from `FundamentalGroup/TwoSimplyConnectedCover.lean` l.7); l.1799/1808 `SphereHomology.twoOpenCover_pathConnectedSpace`, `SphereHomology.twoOpenCover_fundamentalGroup_eq_one` — project namespace `SphereHomology` for generic corollaries
- l.1670–1716 `pushoutToFundamentalGroup`, `fundamentalGroupToPushout` and l.1753 `pushoutEquiv` build the equivalence by hand where the split version uses `Monoid.PushoutI.equivOfCocone` — this copy states the uniqueness half explicitly (`fundamentalGroupToPushout`, docstring l.1704), which the split version lacks
- l.6 `import Mathlib`, l.19 `maxSynthPendingDepth 3`, l.21–26 kitchen-sink `open`, l.28 unused `universe`, l.34 `local notation … SlashAction.map`; no copyright header
- 0 undocumented (this copy is fully documented, unlike the split copy — the docstrings should be ported before deletion); pattern clear after l.500, not read in full
suggestion: port the docstrings and the explicit uniqueness statement (`fundamentalGroupToPushout`) into `VanKampen/Pushout.lean`, then delete this file and the `TriangleRegularBase…` import chain.

## Lib/AlgebraicTopology/Hurewicz/CubeChainDecomposition.lean  (133 declarations, 2268 lines)
verdict: C (project residue in the mathematics: `X : Type` (universe 0) throughout; project-internal references and names)
twin: Kuhn/Freudenthal triangulation of the cube and the Hurewicz cycle of a based `n`-cube (Hatcher §3.B cross product, cited l.39; Hatcher 4.2 Hurewicz; Eilenberg–Steenrod for the prism operator); no Mathlib twin (Mathlib has no singular homology cross product) — genuine gap
findings:
- l.1077 `fundamentalCubeChain`, l.1089 `cubeChain`, l.2045 `cubeChain_eq_sum_simplices` (`[Πⁿ] = Σ_σ sign σ · σ_e`), l.2219 `cubeCycle`, l.2237 `cubeHomologyClass`, l.2244 `cubeHomologyClass_const`: the textbook construction, all `n`; module docstring is Mathlib-style with outline, main results, references, tags; 0 undocumented
- `{X : Type}` (41 occurrences) — every topological space in universe 0, inherited from the project's `SingularChains` development; Mathlib would take `Type u`
- l.780 `private theorem linearMap_zsmul_apply_mo1973_8057` — a `Mathoverflow1973`-derived name; l.38 reference "recorded in `Lib/docs/C.md`, §§3 and 10–11", l.2043 "of the lane's textbook (§9, L5)" — project-internal documents cited as the reference
- l.47 `set_option maxSynthPendingDepth 3`, l.49 `open … Manifold …`; ten `attribute [local instance] SingularHomology.integerLinearMapModule` (l.286–1363) — an instance that should be global in the chains file
- l.57–974 `CubeSubdivision.*` (prism realisation, bad prisms, shuffle vertices, permutation insertion signs): the combinatorial core, correct place, but `badPrism`/`prismDiscrepancy` are proof-step names; pattern clear after l.1100, not read in full
suggestion: lift to `Type u` once `SingularChains` is universe-polymorphic, replace the `docs/C.md`/"lane's textbook" citations by Hatcher §3.B/4.2 and rename the `mo1973` lemma.

# done 82 files

## Lib/AlgebraicTopology/Hurewicz/PrismOperator.lean  (455 declarations, 5303 lines)
verdict: C (two subjects in one file; general prism operator carries the `DegreeTwo.SimplyConnected` name; universe 0; `_mo1973_` names)
twin: Hatcher Thm 2.10 (prism operator, `∂P + P∂ = g# − f#`) and Thm 4.32 at `n = 2` (both named in docstring); no Mathlib twin for either (nearest Mathlib/AlgebraicTopology/SingularHomology/Basic.lean)
findings:
- l.744 `prismOperator`, l.706 `timeSlice`, and `prismOperator_boundary` (`∂(P c) = H₁# c − H₀# c − P(∂c)`): the textbook prism operator for any `H : C(I × A, X)`, correct signs; l.864 `simplexPrismOperator`, l.880 `FaceCompatibleHomotopies` its simplex-family version; this ~300-line section (l.703–996) is library material and every downstream file imports it under the namespace `Hurewicz.DegreeTwo.SimplyConnected`, which names neither the operator nor its generality
- l.5043 `degreeTwoLinearEquiv : Additive (π_ 2 X x) ≃ₗ[ℤ] H_2 X` for `[SimplyConnectedSpace X]`: the textbook degree-two Hurewicz theorem; the ~4,000 lines between (sections l.996–5038: vertex/edge straightening, based triangles, tetrahedron boundary, square rotation `rotationCentered` l.2304, square subdivision, two-triangle decomposition, normalized squares) are the hand-built `n = 2` case of the general argument in `CubeSphere`/`Straightening`, which then uses this file as its base case
- 248 `{X : Type}` vs 42 `Type*`; the prism operator (l.706–996) needs no universe restriction beyond the chain interface's
- 7 `_mo1973_NNNN` private names (l.4405 `basedTriangles_diagonal_mo1973_6743`, l.4458 `triangleQuotient_swapped_upper_mo1973_6748`, …)
- l.65–127 `crossProductTriangle_zero_eq_zeroRight` and the cross-product preliminaries, l.5064–5303 `composeSimplexHomotopies` and `*_const` lemmas (namespace `Hurewicz`, used by `Straightening`) are unrelated to both the prism operator and degree two
- l.55 references cite `Lib/docs/C.md §§6, 8, 12–13`; l.63 `set_option maxSynthPendingDepth 3`, l.65 `open ... Filter Manifold` unused; 0 missing docstrings on 455 declarations; sections are labelled, reading stopped after sampling the section heads and the two main statements
suggestion: split into `PrismOperator.lean` (l.703–996, namespace `SingularChains.Prism` or `Hurewicz.Prism`, `Type*`) and `DegreeTwo.lean` (the rest), and move `composeSimplexHomotopies` to `Straightening.lean`

## Lib/AlgebraicTopology/Hurewicz/Subdivision.lean  (228 declarations, 2582 lines)
verdict: C (`_mo1973_` names; "native" project vocabulary; two namespaces interleaved)
twin: Hatcher Thm 4.32 proof (a cube class is the signed sum of the simplex classes of its Kuhn cells; named in docstring); no Mathlib twin (nearest Mathlib/Topology/Homotopy/HomotopyGroup.lean `GenLoop.transAt`/`Homotopic`)
findings:
- l.2574 `nativeCubeSubdivision_class : Additive.ofMul ⟦p⟧ = ∑ e : Perm (Fin n), cubeOrientation e • basedSimplexClass (nativeBasedCubeSimplex p hp e)` for `{X : Type*}`, `[Nontrivial (Fin n)]`: the general statement, fully general universe (99 `Type*`, 3 `Type`); l.679 `nativeClass`, l.805 `permuteCubeLoop`, l.689 `nativeClass_transAt`: the cube-class calculus used by `CubeGluing`
- "native" (`NativeSubdivision`, `nativeClass`, `NativeCubeInternalBased`, `nativeDuffyCube`, `nativeOrderedDuffyMap`, `NativeChamberChart`) is the project's word for "in `π_n` rather than in homology"; no textbook uses it; Mathlib would say `GenLoop.homotopyClass`/`cubeSubdivision`
- l.886, l.899 (and two more) private `succAbove_lt_prefix_iff_mo1973_8180`, `_8181`: Mathoverflow-ticket suffixes
- namespaces `Hurewicz.SimplexGeometry` (49 declarations: `prefixMinimum`, `extendedMinimum`, `simplexQuotient`, boundary strata l.53–548) and `Hurewicz.NativeSubdivision` (172) interleave; the `SimplexGeometry` half is a self-contained "simplex as quotient of the cube" construction that `CubeGluing`, `Straightening`, `Degree` all extend in place
- l.709 `NativeCubeInternalBased p` is a hypothesis the textbook never states (the cube is constant near the boundary strata); it exists so the subdivision lemma can be applied after `CubeGluing.coherentCubeEndpoint`; fine as a lemma hypothesis but the name says nothing mathematical
- l.38 references cite `Lib/docs/C.md §§9–10` first; l.47 `set_option maxSynthPendingDepth 3`, l.49 `open ... Filter Manifold` unused; 0 missing docstrings on 228 declarations; reading stopped after the section heads and the main statements
suggestion: split the `SimplexGeometry` half into its own file, rename `native*` to `cubeClass*`/`cubeSubdivision*`, and strip the `_mo1973_` suffixes

## Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean  (218 declarations, 4475 lines)
verdict: C (left degree fixed to 1 and 2 where Hatcher is general; half the file in the project namespace despite the docstring; `_mo1973_*` names)
twin: Hatcher §3.B (cross product, Leibniz rule, graded commutativity and associativity; Prop 3B.? via `Δᵖ × Δ^q` triangulation); Mathlib: none (genuine gap)
findings:
- l.30–31 docstring claims "the cross-product declarations use the general `SingularHomology` namespace; historical `PeriodTorusHigherHomology` names are available only through shims"; l.2064–4475 (≈120 declarations: swap homotopy, associator, `crossProductHomologyTwoOne`, `crossProductHomology_natural`) are in `PeriodTorusHigherHomology` — stale sentence
- l.886, 1225, 1853 `crossProductEdge`, `crossProductTriangle`, `crossProductHomology : H₁(X) → Hₙ(Y) → H_{n+1}(X × Y)`: the textbook cross product is `H_p ⊗ H_q → H_{p+q}` for all `p`; the left degree is fixed to 1 (and 2 for the prism), which is the project's need, not the theorem; `formalEdgeCrossProduct`/`formalTriangleCrossProduct` (l.555, 1041) hard-code the `Δ¹ × Δⁿ`, `Δ² × Δⁿ` triangulations instead of the general shuffle formula
- l.97–106 `integerLinearMapModule`, `integerTensorModule`: local `Module ℤ` instance wrappers to dodge a diamond; documented as a workaround (l.68–75) — elaboration residue, not mathematics
- l.116–403, 2533–2640 `integerBilinearRightApply`, `integerBilinearFlip`, `integerBilinearPostcompose`, `integerTrilinearPostcompose`…: `LinearMap.flip`, `LinearMap.compl₂`, `LinearMap.lcomp` exist in Mathlib for any semiring; re-implemented for `ℤ`
- l.1577–1625 `homologyBoundaries`, `homologyLinearMap_ext`, `homologyDesc` are generic `ChainComplex (ModuleCat.{0} ℤ) ℕ` facts (belong in `ModuleHomology.lean`, over any `R`)
- l.2917, 2932 `private def triplePostcomp_mo1973_13949`, `triplePrecompLast_mo1973_13950`
- l.86–88 docstring "Consumers: the Hurewicz lane, the torus lane" — project-plan vocabulary; 0 missing docstrings otherwise; universe-0 `X Y Z : Type` throughout
- pattern clear after l.2100 (each property = formal defect + formal homotopy + affine chain map + boundary + descent); rest sampled only
suggestion: rename the l.2064–4475 block into `SingularHomology`, split it (Swap / Associator / Naturality) into separate files, and state the degree-1 restriction in the docstring or generalise `crossProductEdge` to `Δᵖ × Δ^q` shuffles.

## Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean  (249 declarations, 2856 lines)
verdict: C (one file for four textbook topics; the definition of singular homology itself is buried in a namespace named after a theorem; duplicates the `SingularSmallChains/Barycentric` files)
twin: Hatcher §2.1 Prop 2.21 (small simplices / barycentric subdivision), Thm 2.20 & §2.2 (Mayer–Vietoris); Mathlib `Mathlib/AlgebraicTopology/SingularHomology/Basic.lean` (definition of singular homology), `Mathlib/Algebra/Homology/ShortComplex/ShortExact.lean` (long exact sequence)
findings:
- l.937 `def SingularMayerVietoris.SingularHomology (X : Type) [TopologicalSpace X] (n : ℕ)` and l.941 `singularHomologyMap` — the whole library's definition of singular homology, at line 937 of a Mayer–Vietoris file in namespace `SingularMayerVietoris`; Mathlib would put it in `SingularHomology/Basic.lean` as `SingularHomology`; every other file in the group refers to `SingularMayerVietoris.SingularHomology`
- l.1127–1980 `affineSimplex`, `FormalChains`, `formalCone`, `formalBoundary`, `formalSubdivision`, `formalSubdivisionHomotopy`, `subdivision`, `subdivisionHomotopy`: barycentric subdivision (Hatcher Prop 2.21 proof) — the same material as `Lib/AlgebraicTopology/SingularSmallChains/Barycentric/{AffineSimplex,FormalChains,FormalSubdivision,FormalHomotopy,FormalIteration}.lean` (names `formalCone`, `formalBoundary`, `formalSubdivision` recur there); two implementations of one theorem
- l.2219–2600 `vertexBarycenter`, `exists_lebesgue_number_two`, `meshFactor`, `formalSubdivision_mesh`: the mesh estimate (Hatcher p. 120) — a metric-geometry topic; `exists_lebesgue_number_two` is `lebesgue_number_lemma` for two opens
- l.674–933 `homologyClassOfCycle`, `homologyBiprodEquiv`, `biprodSequence_exact_at_*`: generic `ChainComplex (ModuleCat.{0} ℤ) ℕ` biproduct facts, duplicated by `Coproduct.homologyBiproductEquiv` (l.388 there)
- l.2811–2826 `exact_at_intersection/_pair/_ambient` state the long exact sequence as three `Function.Exact` statements rather than as a `ShortComplex`/`HomologicalComplex` exactness object; fine for a textbook, not Mathlib style
- 0 missing docstrings; module docstring accurate and well-referenced; `X : Type` universe 0 (100 occurrences) mixed with `Type*` (80) in the affine part
- l.80–95 preamble residue (`set_option`, kitchen-sink `open scoped`, `universe u v`, `local infixr " ≫ₚ "`, `local notation … SlashAction.map`)
- pattern clear by l.1200; l.1200–2700 sampled by statement names only
suggestion: extract `SingularHomology`/`singularHomologyMap` into a `Basic.lean` in namespace `SingularHomology`, and replace l.1127–2600 by the `SingularSmallChains/Barycentric` development so the small-simplices theorem is proved once.

## Lib/Analysis/Calculus/MorseLemma.lean  (158 declarations, 2478 lines)
verdict: C (project residue: seven unrelated topics in one file, project namespaces)
twin: Milnor, Morse Theory Lemma 2.2 (Morse lemma) and h-cobordism Thm 2.5 (existence of Morse functions); no Mathlib twin (Mathlib has `Mathlib/Analysis/Calculus/...` but no Morse lemma — genuine gap for l.1142–2035)
findings:
- l.11–52 docstring names Milnor 2.2 / 2.5 with references; every declaration has a docstring (1 missing); the headline `SmoothMorseLemma.exists_signed_morse_chart_of_contDiffOn` l.1993 and `ManifoldMorse.exists_morse_function` l.1131 are textbook statements, general in `E` finite-dimensional and `M` a boundaryless `𝓘(ℝ, E)`-manifold
- the file mixes nine namespaces: `MorsePerturbation`, `ManifoldPerturbation`, `ManifoldMorse`, `SmoothMorseLemma`, `MorseHandle` (Morse theory) with `FlowConstruction` l.533–866 (descent vector fields), `MorseCancellation` l.733, 2356–2478 (closed blocks for handle cancellation), `HolomorphicCousin` l.868–946 (smooth partitions of unity: nothing to do with Cousin or Morse) and `LineBundleTransport` l.947–1001 (cutoff functions); the last two are named for their project consumer, not their content
- l.1142–1187 `contDiff_parametric_intervalIntegral*` and l.1705–1768 `exists_contDiff_extension*` are general calculus facts that Mathlib would place in `Analysis/Calculus/ParametricIntervalIntegral` and `Analysis/Calculus/BumpFunction`; l.988 `LineBundleTransport.exists_interval_cutoff` likewise
- l.1288–1400 `Bilinear`, `SymmetricForm`, `symmetrize`, `congruence`, `raiseIndex` is a symmetric-bilinear-form toolkit that duplicates `LinearMap.BilinForm`/`LinearMap.IsSymm`
- l.7–10 `import Mathlib`, `import all Mathlib.Geometry.Manifold.LocalDiffeomorph`; l.55–70 `set_option maxSynthPendingDepth 3`, kitchen-sink `open scoped … Modular … UpperHalfPlane`, `universe u v` unused, `local notation` for `SlashAction.map` and `Path.trans`: project preamble
- all manifold statements are for `𝓘(ℝ, E)` only (178 occurrences); Milnor's Morse lemma is for manifolds without boundary, so this is acceptable, but a general `ModelWithCorners` version of `IsMorseAt` would be the Mathlib form
- read up to l.1141 and l.1993–2100 in full, statements only afterwards; the pattern is clear
suggestion: split into `MorseLemma.lean` (l.1142–2035), `Morse/Exists.lean` (l.75–1141), `Morse/DescentField.lean` (l.533–866, 2239–2478), and move the partition-of-unity, cutoff and parametric-integral lemmas to their Mathlib-shaped homes, dropping the `HolomorphicCousin`/`LineBundleTransport` namespaces

## Lib/Analysis/Complex/RiemannMapping.lean  (181 declarations, 2411 lines)
verdict: C (project residue: three topics merged, triangle-specific roots, lane narrative in docstring)
twin: Ahlfors Ch. 6 §1 / Rudin RCA Thm 14.8 (Riemann mapping theorem via normal families and the Koebe square-root trick); Carathéodory–Schwarz boundary extension (Ahlfors 6.1.3 / Pommerenke §2); Mathlib/Analysis/Complex/RiemannMapping.lean has only the Koebe step (`exists_mapsTo_unitBall_injOn_deriv_ne_zero`), not the theorem
findings:
- l.11–60 docstring names Ahlfors 6.1 and Rudin 14.8; 0 missing docstrings; the core l.453–800 (`compactSubsets`, `normalizedClass`, `exists_maximal_normalizedMap`, `exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero` l.690, `riemannMap` l.789) is the textbook proof, general in `U : Set ℂ`
- l.23–27 docstring says the boundary lemmas "share this file (lane-A MayerVietoris-style merge, recorded in Lib/reports/A.md)": project process narrative in a library docstring; the file is three namespaces `TriangleRiemannNormalization` (l.80–222), `RiemannMapping`, `RiemannBoundary` (l.267–440, 804–2400)
- l.1563–1937 `principalRoot`, `principalRoot_three_*`, `cubic_sector_slack`, `quartic_sector_slack`, `quarticRootRotation`, `rotatedPrincipalRootFour_*`: the `z ↦ z^{1/3}`, `z^{1/4}` straightening maps for the project's triangle vertices at angles π/3, π/4 (or 2π/3...) — a special case of the general `z ↦ z^{π/α}` corner-straightening (Ahlfors 6.2, Schwarz–Christoffel); the exponent-specific lemmas have no textbook counterpart
- l.2354 `triangleSideParameter`, l.80–222 `TriangleRiemannNormalization.*` and l.310–440 `logHalfStrip`, `onePointDomain*` are the project's triangle/ideal-vertex normalisation
- l.804–966 `openRectangle`, `wedgeIntegral_*`, `isExactOn_openRectangle`, `exists_continuous_primitive_openRectangle` duplicate Mathlib's `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` / primitive-on-convex-set machinery
- l.1056 `exists_analytic_extension_of_vanishing_jump`, l.1239 `exists_analytic_extension_of_modulus_one` are Schwarz-reflection facts that belong in `SchwarzReflection.lean`
- l.6 `import Mathlib`, l.62–77 same kitchen-sink preamble (`maxSynthPendingDepth`, `Modular`, `UpperHalfPlane`, slash notation, `universe u v`)
- read docstring and all statements; sampled l.453–800 and l.1563–1760; pattern clear
suggestion: keep l.453–800 as `RiemannMapping.lean` (Ahlfors 6.1), move `RiemannBoundary.*` to a `Carathéodory`/`SchwarzReflection` file stated for a general corner exponent, and move `TriangleRiemannNormalization`/`principalRoot_three_*`/`rotatedPrincipalRootFour_*` to the project's triangle consumer

## Lib/Geometry/Manifold/Collar.lean  (147 declarations, 2550 lines)
verdict: C (project residue: six unrelated topics in one file, project-shaped statements, plan narrative in docstring)
twin: Lee, Introduction to Smooth Manifolds Thm 6.24 (tubular neighbourhood theorem), Thm 9.25 (collar neighbourhood theorem), Hirsch Ch. 4 §5–6; Milnor h-cobordism §2–3 (level transport by gradient-like flows); no Mathlib twin (genuine gap for tubular neighbourhoods and collars)
findings:
- l.9–41 docstring cites Lee Ch. 10/Thm 6.24 but also "in the level-transport form used by the recognition development. (The plan's Tubular.lean is folded here; see Lib/reports/A.md.)": project process narrative; 0 missing docstrings
- l.582 `NativeEuclideanEmbedding.exists_tubularNeighborhood` and l.1639 `exists_tubularNeighborhood_in_open_of_embedded_closedBall` are the tubular neighbourhood theorem, the second in a specialised form (an embedded closed unit ball `f : D → M` with `finrank D + n = finrank E`, inside a given open `O`, on a compact `M`); the textbook statement is for any embedded submanifold; `NativeEuclideanEmbedding` (a Lib structure: `M` embedded in Euclidean space) is the project's route via Whitney embedding rather than a normal bundle on `M` intrinsically
- l.1707, 1781 `RegularLevel.exists_transverseCollar`, `exists_heightCollar` (Lee 9.25 in the regular-level form, with `letI := chartedSpace hf hreg` in the statement), l.2185–2496 `exists_ambientTransport_of_heightCollar`, `exists_nearby_ambient_level_diffeomorphs`, `AmbientEquivalent`, `exists_levelDiffeomorph_of_ambient`: level-transport machinery (Milnor h-cobordism §3) — a second topic
- l.886–1660 `DiskFraming.*` (smooth frames along a star-convex set, `SmoothRangeTransportOn`, `isOpen_forall_compact` l.1139 and `homotopyTransportDomain` l.1157 at root namespace), l.1875–1990 `SmallPerturbation.*` (`id + small` is a diffeomorphism, bump translations), l.1994–2170 `SupportedDiffeomorph.*` (extension by the identity of a compactly supported diffeomorphism in a chart), l.2532 `SphereCoordinates.ofLinearIsometry`: four further topics, each Mathlib-shaped on its own
- l.8–23 `import Mathlib` plus 16 Lib imports including `Morse.HandleAttachment`, `Topology.Homotopy.HandleRetraction`, `WhitneyEmbedding`: a collar file should not depend on handle attachment; l.36 `set_option maxSynthPendingDepth 3`; all manifolds are `𝓘(ℝ, E)`, `[CompactSpace M]` where Lee's theorems need no compactness (216 occurrences)
- statements read in full; l.79–130, 582–600, 1639–1660, 1707–1716 read; pattern clear
suggestion: split into `Tubular.lean` (l.79–660, 1639), `Collar.lean` (l.673–860, 1690–1870), `SupportedDiffeomorph.lean` (l.1875–2170) and `LevelTransport.lean` (l.2175–2530), state the tubular and collar theorems for non-compact `M` as in Lee 6.24/9.25, and delete the plan narrative
# done 63 files

## Lib/Geometry/Manifold/Flow/HeightTranslating.lean  (106 declarations, 1835 lines)
verdict: C (two subjects: general flow/collar theory plus SignedMorseChart handle machinery; docstring promises absent declarations)
twin: Milnor, Morse Theory, Thm 3.1 (sublevel `M^a` a deformation retract of `M^{a+ε}` via a flow) and Lectures on the h-cobordism theorem §4; no Mathlib twin (Mathlib `Flow` in Topology/Algebra/Flow? has no entry-time or collar API — genuine gap for §"entry time"/"collar")
findings:
- l.16–25 module docstring names as its two main results `FlowConstruction.exists_heightTranslatingFlow` and `exists_regularSublevelHomeomorph_with_level`; neither is in this file (they live in Morse/CubicFlow.lean:148 and Morse/Reeb.lean:573) — the docstring describes a different file; the title "height-translating flows" does not match the content (entry times, flow collars, attaching maps)
- l.661–835 `FlowConstruction.entryTime` (`sInf {t | 0 ≤ t ∧ F t x ∈ A}`), `entryRetraction`, `entryDeformation`, `entryHomotopyEquiv` and l.1236–1745 `FlowCollarData` (`rescale`, `homeomorph`, `exists_absorbingSublevelHomeomorph_with_boundary_orbits`) are stated for an arbitrary `Flow ℝ X` on a topological space: clean, general, textbook (Milnor Thm 3.1's argument made explicit) — the best material in the file, but hidden under the namespace `FlowConstruction`, which names no object (Mathlib: `Flow.entryTime`, `Flow.CollarData`)
- l.59–245 `MorseHandle.unitBallHomeomorph`, `SignedMorseChart.handleBallCoordinates/normHandleMap/attachmentBoundaryData/attachingCoreMap` and l.249–460 descent-model lemmas (`quadratic_descentFlow_lt`, `flow_eqOn_descentModel`) are handle-attachment specifics tied to `ManifoldMorse.SignedMorseChart`, `PuncturedHandle.UnitBall`, `UnitDisk`: they belong in Morse/HandleAttachment, not in a flows file
- l.1118 `exists_absorbingSublevelHomotopyEquiv` and l.1745 carry 12–13 explicit hypotheses (`hdesc`, `hcurve`, `hmono`, `hforward`, `hentry`, `htop`, …) that a textbook packages as "gradient-like field for `f`" and "`A` is forward-invariant absorbing"; a structure (as `FlowCollarData` already does at l.1236) would make these statements readable
- l.1804 `frontier_sublevel_eq_of_strict_flow` is a pure topology fact at the end of the file after the main theorem
- l.7–12 `public import Mathlib` plus four Lib imports; l.34–53 `set_option maxSynthPendingDepth`, kitchen-sink `open scoped … UpperHalfPlane`, unused `universe u v`, unused `local notation`
- 0 missing docstrings (106/106); read statements and the docstrings only, proofs sampled at l.661–760 and l.1745–1835
suggestion: rewrite the module docstring to describe the entry-time/collar theory that is actually here (moving the `SignedMorseChart` attaching-map section to Morse/HandleAttachment) and rename the namespace to `Flow`

## Lib/Geometry/Manifold/Immersion/Relative.lean  (214 declarations, 4647 lines)
verdict: C (omnibus of five topics; `MorseCancellation` names; `Plane := ℝ × ℝ` specialisation; no docstrings)
twin: Hirsch, Differential Topology, Ch. 8 §? (relative immersion/embedding theorems, Whitney's weak theorem — named in docstring, no theorem numbers); Whitney 1936 Thm 5; Mathlib has no immersion-existence or tubular-neighbourhood theory (nearest: Geometry/Manifold/Immersion? only `Immersion` predicate) — genuine gap
findings:
- 0 of 214 declarations have a docstring (`grep -c '^/-- '` = 0); the module docstring itself admits "tubular-neighborhood one-offs", "arc/germ existence one-offs" and "representation-only generality dictated by the twin file" (l.22–35)
- l.65–215 `MorseCancellation.exists_open_isotopic_pointMoving`, `isotopicPointOrbit`, `exists_isotopic_pointMoving_of_path`, and 16 `MorseCancellation.*` names in total (e.g. l.2353 `exists_smooth_path_avoiding_closed_image`, l.3142 `exists_clean_arc_with_local_endpoint_germs`, l.3536 `sheetAxisShuffle`): homogeneity-of-manifolds and path-avoidance lemmas that are general (Hirsch Ch. 8 / Milnor h-cobordism Lemma 6.?) but named after their consumer
- l.981 `abbrev PlaneImmersion.Plane := ℝ × ℝ` and l.2033 `ManifoldImmersion.exists_relative_compact_embedding (f : C(Plane, N)) (hdim : 5 ≤ finrank ℝ G)`: the headline relative embedding theorem is stated only for a 2-dimensional source (`2·2+1 = 5`); Hirsch/Whitney state it for any compact `m`-manifold into `N^n`, `n ≥ 2m+1`; l.2096 `…_twoDimensional` confirms the specialisation is deliberate
- l.393–610 `ChartMapPerturbation`, l.981–1275 `PlaneImmersion` (`firstCollision`, `badFirst`, `dimH_bad_parameters_le` — a Hausdorff-dimension/Sard-style parametric transversality argument), l.2598–2733 `WeightedPerturbation`, l.3778–4660 `FrameField`/`AxisCoordinates`/`LinearFramePaths`: five namespaces, each a separate file's worth, with no section docstrings (`/-!` headers: none found)
- l.3263–3484 `exists_*_tubularNeighborhood_of_embedded_starConvex*` are general tubular-neighbourhood existence statements (Hirsch Ch. 4 §5) misfiled under `Immersion/`
- l.6–16 `public import Mathlib` plus eight Lib imports (Morse.Existence, SurgeryWindows, CubicFlow — Morse-theory dependencies in an immersion file signal the consumer-driven organisation); l.44–60 `set_option maxSynthPendingDepth`, kitchen-sink `open scoped`, unused `universe u v`
- read: module docstring, all 214 statement heads, and the statements at l.65, l.981, l.2033, l.3142 in full; stopped there
suggestion: split into `Immersion/Relative` (l.615–2286 relative immersion/embedding, generalised from `Plane` to any compact source with `n ≥ 2m+1`), `Isotopy/PointMoving`, `TubularNeighborhood/StarConvex`, `FrameField`, and add docstrings; drop the `MorseCancellation` prefix

## Lib/Geometry/Manifold/Morse/Cancellation.lean  (137 declarations, 3814 lines)
verdict: C (headline theorem is textbook-grade but the file is five namespaces of proof machinery in project ("native") vocabulary)
twin: Milnor, Lectures on the h-cobordism theorem, Thm 5.4 (first cancellation theorem — named in docstring) for l.3597 `cancel_of_transverse_level_isotopy`; no Mathlib twin (no Morse theory in Mathlib) — genuine gap
findings:
- l.3597 `MorseCancellation.cancel_of_transverse_level_isotopy`: general (`finrank E = m+1`, adjacent indices via `SignedMorseChart.weights`, compact `M`), but ~25 explicit hypotheses (`hV hzero hdesc F hF hinj hpc hqc hl hu hpair ha hb hpc' hqc' hband hreg heqp heqq`, then `∀ D : Diffeomorph … ` of the regular level) where Milnor's statement has three: gradient-like field, one connecting trajectory, transversality; a `structure` (as l.809 `NativeConnectionCancellationData` already does) should carry them
- the word "native" (chart-native data) occurs 144 times — `nativeCubicDescent`, `NativeConnectionCancellationData`, `exists_native_backward_morse_level_exit`, `nativeMorseIndex`, `nativeMorseCount` (l.3710): project vocabulary with no textbook counterpart; the Morse index and count should be `ManifoldMorse.index`/`ManifoldMorse.count`
- five namespaces in one file: `MorseCancellation` (cubic model, index, count), `FlowCancellation` (l.859–2370: Lyapunov residence bounds, `logarithmicCoordinate`, `descentBlend`, `flowTube`, `bandReplacement` — flow-analysis lemmas independent of Morse theory), `NativeCubicCancellation`, `MorseCancellationPreservation` (l.2471–2498, generic "Morse iff Morse on germs" facts), `TransverseGerms` (l.3023–3384, transversality of sheet factorisations) — at least three files' worth
- l.62–222 cubic model `cancelledDescent`, `exists_cubic_field_cancellation` on `Model m = ℝ × (Fin m → ℝ)` and l.2374–2445 `hessian`, `cubic_isMorse`: the local model of Milnor §5 — general and good; l.1742–1850 `logarithmicCoordinate`, `exists_logarithmic_cutoff` are one-variable calculus lemmas (`Analysis/SpecialFunctions`) placed here
- 1 of 137 declarations lacks a docstring; module docstring has main results, reference, tags — good; l.6 `import Mathlib`, l.34–56 `set_option maxSynthPendingDepth`, kitchen-sink `open scoped … UpperHalfPlane`, unused `universe u v`, unused `local notation`; non-`module` file
- read: module docstring, all 137 statement heads, l.809 structure and l.3597 statement in full; stopped there
suggestion: split off `FlowCancellation` (flow/Lyapunov analysis) and `TransverseGerms` into their own files, rename `native*` to plain Morse vocabulary, and restate l.3597 with a hypothesis structure

## Lib/Geometry/Manifold/Morse/Connection.lean  (231 declarations, 8180 lines)
verdict: C (8,000 lines of proof machinery for one step of Milnor Thm 5.4 — the "unique transverse connection ⇒ cubic field chart" lemma — in project ("native") vocabulary across eight namespaces)
twin: Milnor, Lectures on the h-cobordism theorem, Thm 5.4 and its preliminary Lemmas 5.1–5.3 (the assertion that the gradient-like field near the single trajectory can be put in the cubic model form) — named in docstring; no Mathlib twin (no Morse theory, no flow-box/suspension theory in Mathlib) — genuine gap
findings:
- l.8–20 module docstring is a list of 20 sub-topics ("clock, chart and suspension machinery … cylinder holonomy, phase clocks and phase flow coordinates …") and states the file was made by merging two former files; it names one main result, `MorseCancellation.exists_full_cubic_chart_from_corrected_cylinder` (l.7874); no `## Main results` list for the other 230 declarations; 31 `/-!` section headers do the outlining
- eight namespaces in one file: `MorseCancellation`, `FlowSuspension` (l.73–3100, 5783–6160, 8048–8120: the suspended flow `nativeSuspensionFlow`, level cylinders, holonomy), `FlowCancellation`, `FlowTimeChange` (l.1566–1940, 6164–6870: time changes, clocks, `PhaseFlowCoordinates`), `TransverseGerms` (l.3104–3160, 4275–4520, 5093–5760), `SignedCoordinates` (l.4852–4955: pure `Fintype`/`Fin` sign-enumeration combinatorics), `FieldChartGluing` (l.7102–7640: gluing three flow-box charts), `SmoothODE` (l.301, one lemma) — each is a separate subject; `FlowTimeChange` and `FieldChartGluing` have textbook content (flow-box theorem, Lee Thm 9.22; time reparametrisation of flows) hidden under Morse-specific names
- "native" occurs 403 times in names/statements (`exists_native_vertical_field_replacement`, `nativeSuspensionFlow`, `native_no_return_of_supported_perturbation`, `exists_native_phase_realization`, …): chart-native data is the project's private notion; a textbook would say "in a flow-box chart"
- l.972–1280 `nativeBeltArc`, `nativeLowerMeridian`, `nativeUpperMeridian`: belt-sphere arcs/meridians of the specific surgery, feeding BeltCancellation.lean — proof-step definitions with no counterpart in Milnor
- l.4852–4955 `SignedCoordinates.exists_adjacent_sign_enumerations`, `negative_card_split` (duplicated as `MorseCancellation.negative_card_split` in Birth.lean:815) and l.502 `interior_zero_product_empty`, l.478 `compact_partial_chart_image_nowhereDense`: general combinatorics/topology lemmas misfiled
- 0 missing docstrings (231/231); l.6 `import Mathlib`, l.26–48 `set_option maxSynthPendingDepth`, kitchen-sink `open scoped … UpperHalfPlane`, unused `universe u v`, unused `local notation`; non-`module` file
- read: module docstring, all 31 section headers, all 231 statement heads, l.53 in full and the proof of l.7874 sampled at l.7999–8010; stopped there — pattern (one giant chain of "exists_native_…" existence lemmas) was clear by l.3000
suggestion: split by namespace into `Flow/TimeChange.lean`, `Flow/Suspension.lean`, `Flow/FieldChartGluing.lean` (each with a textbook-style docstring: flow box, time change, suspension) and keep only the `MorseCancellation` chain here; replace "native" by "flow-box chart" throughout

# done 15 files

## Lib/Geometry/Manifold/Morse/Cubic.lean  (143 declarations, 2706 lines)
verdict: C (project residue in the mathematics: five unrelated topics in one file, `native_*`/`AdaptedWindows` vocabulary, general facts filed under `MorseCancellation`)
twin: Milnor, Lectures on the h-cobordism theorem, Thm 4.1 (cubic model x³/3 + tx + Σσᵢyᵢ²); no Mathlib twin (nearest: Mathlib/Analysis/SpecialFunctions/Artanh.lean for l.2525–2668)
findings:
- l.15–35 module docstring names Milnor Thm 4.1 and references; but l.25–28 records file history ("material of the former `Morse/Cancellation.lean`", import order `Cubic → CubicFlow → …`) — maintenance note, not library text
- l.57–870 (`nonempty_adaptedSurgeryWindows`, `exists_native_morse_basin_block`, `native_attaching_core_flow`, `native_belt_core_basin_iff`, …): 30 theorems on adapted windows/basin blocks whose hypotheses are the project's `AdaptedWindows E f` / `MorseSurgeryData` packages; `native_` is project jargon with no textbook counterpart
- l.723–850 `FlowCancellation.exists_local_strict_flow_descent`, `forwardInvariant_sublevel_of_boundary`, `flow_level_time_unique`: general `Flow ℝ X` facts on a topological space, unrelated to the cubic model; belong in `Dynamics/Flow`
- l.885–990 `Model`, `cubic`, `differential`, `critical_iff`, `cubic_critical_values`: the textbook model, generic in `m`, correctly stated; the one part that is library-ready as is
- l.1105–1225 `LocalFunctionReplacement.replace*` (generic replacement of a function by a chart model on a compact support) is a third subject; fine mathematics, misplaced
- l.2525–2560 `MorseCancellation.hasDerivAt_tanh`, `strictMono_tanh`, `range_tanh`, `tendsto_tanh_atTop/atBot`, l.2659 `contDiffAt_artanh`: real-analysis facts under a Morse namespace; Mathlib has `Real.tanh_bijOn`, `Real.tanh_injective`, `Real.tanh_lt_one`, `Real.artanh_tanh` (Analysis/SpecialFunctions/Artanh.lean); missing pieces should go there under `Real.`
- l.1497–1650 `splitLinear`/`splitEquiv` over `Option (Fin m) ≃ Fin n`: an ad-hoc reindexing equivalence that exists only to feed the alignment step; Mathlib would use `Fin.consEquiv`/`finSuccEquiv`
- l.40 `set_option maxSynthPendingDepth 3`; l.44–47 kitchen-sink `open scoped … Modular UpperHalfPlane`; l.49 `universe u v` unused; l.13 `import all Mathlib.Geometry.Manifold.LocalDiffeomorph` in addition to `import Mathlib`
- docstrings: 1 declaration without one (good density otherwise); stopped reading proofs after l.1100, statements read throughout
suggestion: split into `Morse/CubicModel.lean` (l.885–1100, 1228–1420, 2562–2706), `Dynamics/Flow/Sublevel.lean` (l.723–850), `Manifold/LocalReplacement.lean` (l.1105–1225), and a `Real.tanh` upstream patch; leave the `native_*`/`AdaptedWindows` block under Hopf/Proof.

## Lib/Geometry/Manifold/Morse/Existence.lean  (117 declarations, 2247 lines)
verdict: C (project residue in the mathematics: three subjects — existence of Morse functions, `SignedMorseChart` attaching/belt-core geometry, Whitney smoothing of continuous maps — under one docstring that names only the first)
twin: Milnor, h-cobordism Thm 2.5/2.7 (existence, distinct critical values) for l.383–560; Hirsch, Differential Topology Thm 2.2.6 / Lee, Smooth Manifolds Thm 6.26 (Whitney approximation) for l.1173–2247; no Mathlib twin (Mathlib has no Morse functions and no smoothing theorem)
findings:
- l.15–33 docstring: "Every compact smooth manifold admits a Morse function (Milnor Thm 2.5), built by chart-wise perturbation"; but `exists_morse_function E M` is imported (used l.559), not proved here; the file's own contribution is `exists_distinct_critical_values` (l.502) and `exists_morse_function_with_distinct_critical_values` (l.551, Milnor Thm 2.7) — docstring names the wrong theorem
- l.59–1160 (`SignedMorseChart.exists_attachingUnionHomeomorph_with_level_and_orbits`, `FollowsModelBoundaryOrbits`, `beltCoreMap`, `attachingCoreMap_isClosedEmbedding`, `SurgeryBoundaryPair.changeNewBoundary`, `ClosedCover.frontierLevelHomeomorph`): 45 declarations of handle-attachment geometry not mentioned in the docstring; belongs in `Morse/HandleAttachment.lean`
- l.1173–2247 `ManifoldSmoothing.*`, `ChartMapPerturbation.*`, `HomotopicRelWithin` (`exists_smooth_map_homotopic` l.2182: every continuous map from a compact manifold to a boundaryless manifold is homotopic to a smooth one): textbook Whitney approximation, general in `I J`, library-ready but has nothing to do with Morse existence; should be `Geometry/Manifold/SmoothApproximation.lean`
- l.1812 `HomotopicRelWithin f g C K O` (root namespace) extends Mathlib's `ContinuousMap.HomotopicRel` with a `MapsTo` constraint; Mathlib naming would be `ContinuousMap.HomotopicRelWithin` or a `Homotopy.MapsTo` predicate
- l.1173 `flattenTime` with the ad-hoc `1/3, 2/3` constants (l.1184, 1191) repeated in statements rather than a `variable`
- l.942–990 `PartialChart.restrictSource/restrictTarget/bijective_mfderiv`: generic partial-chart API, misfiled
- statements generic in `E M` (`Type*`, `IsManifold 𝓘(ℝ,E) ∞ M`), 0 missing docstrings, `[milnor65]` reference present
- l.38 `set_option maxSynthPendingDepth 3`, l.41–45 `open scoped … Modular UpperHalfPlane`, l.47 `universe u v` unused; stopped reading proofs at l.600, statements read throughout
suggestion: split into `Morse/Existence.lean` (l.252–560, keep docstring corrected to Thm 2.7), `Morse/HandleAttachment.lean` (l.59–1160) and `Geometry/Manifold/SmoothApproximation.lean` (l.1173–2247) with its own Hirsch/Lee docstring.

## Lib/Geometry/Manifold/Morse/OrderedCancellation.lean  (86 declarations, 2104 lines)
verdict: D (not library material: docstring says "Moved verbatim from `Hopf/SphereTopology.lean`"; the file is the project's minimal-excellent-Morse-system pipeline with 76 undocumented declarations)
twin: Milnor, h-cobordism §4 (Rearrangement) and Thm 8.1 (cancellation of a 0/1 pair) for the ideas; no Mathlib twin
findings:
- l.14–24 docstring: inventory paragraph plus migration receipt ("base `304a0fea`; see `Lib/reports/integration-4/spheretop-moves.md`"); promises `exists_outer_index_minimal_ordered_morse_system` (l.64) which is not in this file (it is Morse/SurgeryCollapse.lean:3182)
- 76 of 86 declarations have no docstring (`nativeBeltTubeSource` l.115, `beltBallCoordinates` l.214, `exists_flow_preserving_value_exchange` l.668, `cancel_unique_zero_one_connection` l.902, `nativeIndexDisorder` l.1354, `exists_middle_index_blocks` l.2022, …)
- universes inconsistent within the file: `{E M : Type}` at l.91–330, 971–1100, 1975–2104 versus `Type*` at l.338–1960
- l.1268 `exists_minimal_excellent_morse_system (E M)`: "there is a Morse function with an `AdaptedWindows` package and the least number of critical points among functions with distinct critical values" — the only statement of textbook shape, but its conclusion `∃ _ : AdaptedWindows E f` is the project's package
- l.83–90 `IntLinearAutomorphism.apply_eq_mul`, `apply_one_eq_one_or_neg_one` (`e : ℤ ≃ₗ[ℤ] ℤ`): Mathlib has `Int.isUnit_iff`/`Int.units_eq_one_or`; l.971–1200 `componentChainWeight`, `zeroChainCycle`, `pathConnectedSpace_of_homologyZero_injective` (`H₀` detects path components) is Hatcher Prop 2.7, hidden here without docstrings and over `Type`
- l.1203–1250 `isMorseAt_neg`, `isMorse_neg`, `nativeMorseIndex_neg_add`, `nativeMorseCount_neg`: index of `−f` is `n − index f` (Milnor Morse Theory §2) — textbook, undocumented, belongs in `Morse/Index.lean`
- l.542 `nativeIndexThreeAttachingSphere`, l.1140 `native_index_one_excluded`, l.2387 (Rearrangement) `pathConnectedSpace_index_three_upper_level`: fixed indices 0/1/3 of the W4W1 argument
- l.70 `set_option maxSynthPendingDepth 3`, l.73–77 `open scoped … Modular UpperHalfPlane`, l.79 `universe u v` unused
- read all statements; proofs not read (pattern clear at l.340)
suggestion: return the file to `Hopf/Proof`; carve out `isMorse_neg`/`nativeMorseIndex_neg_add` (to Index.lean) and `pathConnectedSpace_of_homologyZero_injective` (to the singular-homology files) with docstrings and `Type*`.

## Lib/Geometry/Manifold/Morse/Rearrangement.lean  (116 declarations, 2784 lines)
verdict: C (project residue in the mathematics: four subjects the docstring itself calls "the band-cancellation tail of the toolbox" and "rearrangement stragglers"; `NativeTransversality`/`native_*` vocabulary; index-3 statement)
twin: Milnor, h-cobordism Thm 4.1 and §4 (rearrangement), for l.376–810 only; Mathlib/Analysis/SpecialFunctions/SmoothTransition.lean for l.816–880 (Mathlib has `Real.smoothTransition.monotone`, `contDiff`, but no derivative-positivity or strict monotonicity — genuine upstream gap)
findings:
- l.35–36 "## Main definitions and results: `MorseRearrangement.exists_morse_rearrangement_of_no_connection` — the Rearrangement Theorem"; that theorem is in Morse/RearrangementTheorem.lean:1048, not here — the docstring names another file's result as its own
- l.16–20, l.30–33 outline admits the file is a staging area: "the band-cancellation tail of the toolbox", "`NativeTransversality.Patch` and the rearrangement stragglers"
- l.376–510 `RegularHeightCoordinates.heightMap/triangularEquiv/longitudinalDiffeomorph` and l.514–710 `MorseRearrangement.IntervalTranslation`, `exists_increasing_interval_translation`, `blendHeight`: the actual Milnor §4 machinery (a diffeomorphism of `ℝ` moving `x` to `y` supported in `(a,b)`, blended along a height function); general, documented, library-ready
- l.816–880 `MorseCancellation.expNegInvGlue_hasDerivAt`, `smoothTransition_deriv_pos`, `smoothTransition_strictMonoOn`, `exists_unique_smoothTransition_time`: real-analysis facts about `Real.smoothTransition` filed under a Morse namespace; should be `Real.smoothTransition.deriv_pos`/`strictMonoOn` upstream
- l.885–1300 `LongitudinalTubeMotion` (structure with `native_axis`, `native_germ` fields l.1016–1026), `exists_clean_two_sheet_arc_avoiding`: Whitney-trick tube geometry, second subject
- l.1632–1700, 2115–2280 `FlowCancellation.native_flow_eq_on_positive_halfline`, `exists_native_smooth_time_germ`, `exists_native_level_flow_cylinder`; l.2387 `AdaptedWindows.pathConnectedSpace_index_three_upper_level`: `AdaptedWindows` hypotheses and a fixed index 3 — the project's dimension-6 argument
- l.2413–2784 `MorseRearrangement.native_transverse_dimension_bound`, `NativeTransversality.Patch/exists_finite_patch_diffeomorph/exists_ambient_transverse_diffeomorph`: general-position (transversality by ambient isotopy) — a third subject that belongs beside `Geometry/Manifold/Transversality/`
- l.2081–2115 `SmoothODE.scalar_partial_invertible`, `exists_smooth_scalar_time_germ`: implicit-function-theorem germ for a scalar time; fourth subject
- 0 missing docstrings; l.54 `set_option maxSynthPendingDepth 3`, l.57–61 `open scoped … Modular UpperHalfPlane`, l.63 `universe u v` unused
- read all statements; proofs sampled to l.700, then stopped (pattern clear)
suggestion: keep l.376–810 as `Morse/Rearrangement.lean` with a corrected docstring (main result: `exists_increasing_interval_translation_with_exterior_germs`), move `smoothTransition_*` to `Lib/Analysis/SpecialFunctions/SmoothTransition.lean` under `Real.smoothTransition`, and `NativeTransversality` to `Transversality/AmbientIsotopy.lean`.

## Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean  (231 declarations, 5437 lines)
verdict: D (a 5,400-line "moved verbatim from Hopf/SphereTopology.lean" dump: zero docstrings, dimension-6 hypotheses, `mo1973_` names, and a dozen unrelated topics; the reusable parts are buried in proof-specific glue)
twin: Milnor, Lectures on the h-cobordism theorem §§4–8 (rearrangement, cancellation, first/second cancellation theorems) and Smale's minimal-Morse-function programme for the ordered/minimal-system results; Hatcher Ex. 2.2 / Prop 2.22 for the one-point-collapse and sphere-puncture homology; Mathlib nearest: `Mathlib/Geometry/Manifold/Instances/Sphere.lean` (`stereographic'`) for `OnePointCover.punctureHomeomorph`
findings:
- l.63–77 module docstring is a receipt ("Moved verbatim from `Hopf/SphereTopology.lean` (base `b78cfee8`, second pass); see `Lib/reports/integration-4/spheretop-moves.md`"), not a description of a theorem; names no textbook result; 0 of 231 declarations carry a docstring (`grep -c '^/--'` = 0)
- l.545, 682, 865, 895, 1639, … twelve statements carry `(hdim : Module.finrank ℝ E = 6)`, and `Hemisphere.Sphere 2` appears 39 times: the middle-block/index-2/index-3 machinery (`AdaptedWindows.exists_middle_block_realization`, `SurgeryWindows.indexTwoBasis`, `middlePresentation`, `middleMatrix`) is the project's 6-manifold argument, not a textbook statement
- l.3393 `private def OnePointCover.spherePunctureHomeomorph_mo1973_5327`, l.4417 `sign_factor_mo1973_5719`, l.4602 `identity_center_mo1973_5731`: Mathoverflow-1973-style names, forbidden vocabulary for library code
- 69 statements bind `{E M : Type}` (universe 0) against 73 with `Type*`; the same file mixes both conventions for the same objects (`MorseSurgeryData`, `SurgeryWindows`)
- topics mixed: `PuncturedBall` deformation (l.95–130), belt-tube meridian homotopies (l.132–236), `AdaptedWindows` level transports (l.238–1010, 2278–2440, 2536–2680, 2860–3180), `EmbeddedCellAttachment` long exact sequence (l.1065–1260), `MorseSurgeryData` homology exactness (l.1354–1600), cancellation/minimal Morse systems (l.1955–2530, 3182), sphere-filling/immersion extension (l.2684–2860), `DiskOnePointCollapse`/`ClosedHandleCore.collapseMap` (l.3242–3390), `OnePointCover` (l.3388–3460, a genuine small library: `punctureHomeomorph`, `oldPatch_contractible`), `SphereNormalCoordinates`/`SpherePoint` Jacobian-sign bookkeeping (l.3907–5110), index-2/3 presentations (l.5124–5437)
- l.3182 `exists_outer_index_minimal_ordered_morse_system`, l.2440 `exists_index_ordered_morse_system_preserving_critical_points`, l.2493/2511 `minimal_excellent_morse_*_count_one`: these are the genuinely textbook targets (Milnor h-cobordism Thm 4.8 rearrangement, Smale's "one minimum, one maximum" for a connected closed manifold), stated for general `E`, `M`, but wrapped in `AdaptedWindows`/`nativeMorseIndex`/`nativeMorseCount` project data with no docstring
- l.3388/4791 `instLocal1 : Fact (finrank (EuclideanSpace ℝ (Fin (n+1))) = n+1)` duplicated twice under two namespaces; `attribute [local instance] … in` repeated per declaration instead of one `section`
- l.6–61 fifty-six imports including `Lib.Algebra.Module.IntegerPresentation` twice (l.42, l.50); l.79 `set_option maxSynthPendingDepth 3`, l.83–86 kitchen-sink `open scoped … Modular … UpperHalfPlane`, l.88 `universe u v` unused
- reading stopped after sampling each namespace block and the closing 80 lines (l.5363–5437); proofs not read
suggestion: this file cannot be upgraded in place; extract the three reusable islands (`OnePointCover.punctureHomeomorph`+`oldPatch_contractible` → Topology/OnePointCollapse, `PuncturedBall.sphereHomotopyEquiv` → beside `PuncturedRadial`, `EmbeddedCellAttachment.cell_exact_*` → AlgebraicTopology) with docstrings, and move the rest (everything with `hdim = 6`, `Hemisphere.Sphere 2`, `mo1973_`) to `Hopf/Proof`.

## Lib/Geometry/Manifold/Morse/SurgeryWindows.lean  (119 declarations, 1980 lines)
verdict: C (well-documented and general, but six unrelated toolkits precede the surgery structures, three Hausdorff-dimension lemmas are declared twice, and "simply connected" is spelled as an ad-hoc `circle_nullhomotopies` predicate)
twin: Milnor, Lectures on the h-cobordism theorem §3–4 (named in docstring with `[milnor65]`, `[milnor63]` references); Mathlib nearest: Mathlib/Topology/MetricSpace/HausdorffDimension.lean (`dimH_image_le_of_locally_lipschitzOn`, `dense_compl_of_dimH_lt_finrank`) for §1, `SimplyConnectedSpace` for the nullhomotopy predicates
findings:
- l.13–55 module docstring is complete (statement, outline, main results, references, tags); 119/119 declarations carry docstrings; all statements are over general `E`, `M` with `Type*` — the best-documented file in the group
- l.78/1097 `GeneralPosition.dimH_image_chart_le` vs root `dimH_image_chart_le`, l.119/1126 `dimH_image_manifold_le`, l.139/1146 `dense_compl_manifold_image`: each proved twice (once with `ContMDiffOn` on an open set, once with `[I.Boundaryless]`); one of each pair should go
- l.765 `ImageComplement.circle_nullhomotopies`, l.780/811/877/1465/1484/1503/1689 `*_circle_nullhomotopies*`: the hypothesis `∀ f : C(Hemisphere.Sphere 1, X), ∃ c, f.Homotopic (const c)` is `SimplyConnectedSpace X` (Mathlib, `simply_connected_iff_paths_homotopic`); an ad-hoc spelling repeated in eight statements
- l.609–735 `Hemisphere.Ambient/Ball/Sphere/point`: a hand-rolled model of `S^n` as two hemispheres; `Hemisphere.Sphere n` is `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1` (Mathlib's sphere), so the namespace duplicates a Mathlib type with a nonstandard name that then leaks into every downstream file
- l.30 docstring outline item 2 names a "`NoExotic` dimension cluster"; `NoExotic` occurs nowhere else in the file (stale name from the project's original file)
- file has seven topics before its subject: Hausdorff dimension of smooth images (l.75–230, 1086–1160), avoidance patches (l.230–445), image complements (l.446–545, 737–907), disk double (l.546–605), hemisphere coordinates (l.606–735), homotopy extension off a closed set (l.1004–1085), zero-avoidance cutoffs (l.1224–1375); the surgery data structures start at l.1534 of 1980
- l.1227–1360 `RealIntervalProgress.progress`, `ZeroAvoidanceCutoff.weight/blend/homotopy` are elementary real-analysis cutoffs; belong in Topology/UrysohnsLemma-style helper or Analysis, not Morse
- l.59 `set_option maxSynthPendingDepth 3`, l.63–66 kitchen-sink `open scoped … Modular … UpperHalfPlane`, l.68 `universe u v` unused, l.72–73 `≫ₚ`/`SlashAction` local notations unused
suggestion: split into `GeneralPosition.lean` (Hausdorff-dimension avoidance, deduplicated), `Hemisphere.lean` (or replace by Mathlib's sphere), and `Morse/SurgeryData.lean` (l.1534–1980 only), and replace every `circle_nullhomotopies` hypothesis by `[SimplyConnectedSpace _]`.

## Lib/Geometry/Manifold/Transversality/Basic.lean  (135 declarations, 2903 lines)
verdict: C (general statements but `Native*` vocabulary throughout, ~45 declarations of Morse belt-coordinate machinery in a transversality file, docstring promises four families that do not exist, 133 of 135 declarations undocumented)
twin: Hirsch, Differential Topology Ch. 2–3 and Guillemin–Pollack Ch. 2 (named in docstring); Palais's disc theorem for `DiskShrinking.exists_embedded_disk_isotopy_of_same_center` (l.2792; Hirsch Thm 8.3.1); Mathlib nearest: Mathlib/Geometry/Manifold/LocalDiffeomorph, no transversality/isotopy API in Mathlib (genuine gap)
findings:
- l.16–48 module docstring promises `NativeTransversality.Patch`, `WeightedPerturbation`, `GeneralPosition` avoidance lemmas and a "`NoExotic` dimension cluster"; none is declared in this file (`Patch`, `WeightedPerturbation`, `NoExotic`, `GeneralPosition` each occur only in the docstring; the `GeneralPosition` lemmas live in `Morse/SurgeryWindows.lean`) — stale outline
- only l.69 and l.93 (`Diffeomorph.toPartialDiffeomorph'`, `IsLocalDiffeomorph.diffeomorph'`, both "transparent variants" of Mathlib declarations) have docstrings; 133 of 135 missing
- l.127 `NativeSubmersion.*`, l.363 `exists_null_exceptional_native_translations`, l.527 `NativeTransversality.At`, l.659 `TransverseGerms.native_transversality_partial_diffeomorph_iff`, l.1066 `NativeParametrization.*`, l.2273 `exists_native_disk_germ_alignment`: "native" is project vocabulary with no mathematical content; Mathlib would say `Submersion`, `IsTransverseAt`, `exists_transverse_translation`
- l.527 `NativeTransversality.At f g x y : Prop := g y = f x → Surjective ((mfderiv f x).coprod (mfderiv g y))` is the textbook definition of `f ⋔ g` at `(x, y)` (Guillemin–Pollack §2.3); it deserves a Mathlib-style `IsTransverseAt` name and a docstring
- l.703–1060 `MorseHandle.ambientMap_*`, `SignedMorseChart.belt*` (14 declarations), `MorseSurgeryData.beltNormal*` (11 declarations): Morse surgery belt-neighbourhood coordinates, forcing `import Lib.Geometry.Manifold.Morse.SurgeryWindows` into a transversality file (transversality is a prerequisite of Morse surgery, not the other way round); belongs in `Morse/`
- l.1505–1570, 2048–2170 `LinearFramePaths.*` (path-connectedness of `SL_n(ℝ)`, diagonal/transvection paths): pure Lie-group topology, no transversality; Mathlib has `Matrix.SpecialLinearGroup` — check for an existing connectedness result before keeping
- l.2324–2560 `SmoothRadial.*`, `DiskShrinking.scale/family` are the radial-diffeomorphism and disc-shrinking constructions; l.2792 `exists_embedded_disk_isotopy_of_same_center` (two embedded discs with the same centre are ambiently isotopic, `hE : 2 ≤ finrank E`, codimension `n > 0`) is the disc theorem — the file's real result, unnamed as such in docstring and undocumented
- all statements are for `ℝ`, `∞`, general `E`, `M`, `ModelWithCorners` where relevant (`Type*` throughout, no dimension pins): the mathematics is general
- l.56 `set_option maxSynthPendingDepth 3`, l.60–63 kitchen-sink `open scoped … Modular … UpperHalfPlane`, l.65 `universe u v` unused; l.8/15 imports both `Mathlib` and `Mathlib.Geometry.Manifold.LocalDiffeomorph`
- reading stopped after the statement list and the main statements at l.127, 527, 2792, 2837; proofs not read
suggestion: move the `MorseHandle`/`SignedMorseChart`/`MorseSurgeryData` block (l.703–1060) to `Morse/`, rename `NativeTransversality.At` → `IsTransverseAt` (and drop "native" everywhere), and rewrite the module docstring around the disc theorem and the transversality relation that the file actually proves.

## Lib/Geometry/Manifold/Whitney/CleanStrips.lean  (140 declarations, 2532 lines)
verdict: C (general-dimension statements, but eleven "families" in one verbatim-moved file, `Native*`/`native_` names, a Morse belt-intersection block inside a Whitney file, and 0 of 140 docstrings)
twin: Milnor, Lectures on the h-cobordism theorem §§5–6 (named in docstring); `finite_transverse_intersections` (l.567) and `isDiscrete_transverse_intersections` (l.546) are Guillemin–Pollack §1.5/§2.3 (transverse complementary compact submanifolds meet in finitely many points); Mathlib: none (genuine gap)
findings:
- l.14–20 module docstring is the same move receipt as `AnnularExtension.lean` ("Moved verbatim … the families here are `TransverseCoordinates`, `NativeEuclideanEmbedding.SmoothRetraction`, `SphereBoundary`, `SphereNormalCoordinates`, `ManifoldMorse.MorseSurgeryData`, `StripCoordinates`, `StripNormalData`, `CleanCornerPatch`, `CleanStripPatch`, `WhitneyPairModel`, `CleanBigonBoundary` … the file order is the dependency order"); no `## Main results`
- 0 of 140 declarations carry a docstring
- l.216 `exists_simultaneous_sheetChart`, l.274 `exists_clean_simultaneous_sheetChart`, l.466 `exists_clean_crossingChart`, l.546/567 `isDiscrete/finite_transverse_intersections`: correctly general (`hdim : finrank D + finrank Z = finrank E`, `Type*`, compact `M`), the textbook "transverse crossing chart" lemmas — the file's upstreamable core, in the root namespace without docstrings
- l.767–905 `ManifoldMorse.MorseSurgeryData.beltNormalReference/beltIntersectionJacobian/beltIntersectionSign/beltIntersectionCount/finite_beltIntersectionPoints`: Morse-surgery belt-sphere intersection numbers (Milnor h-cob §6 intersection number, but bound to `MorseSurgeryData`); belongs in `Morse/`, not `Whitney/`
- l.81–200 `NativeEuclideanEmbedding.SmoothRetraction.sheetCoordinates*`, l.1294 `StripNormalData.native_derivative_factor`, l.1674 `exists_native_clean_corner_of_parametrizations`, l.2218/2234 `injective_nativeDerivative_*`: "native" project vocabulary in names
- l.982–1300, 1370–1620 `StripCoordinates.*`/`StripNormalData` (strip charts near a corner, `Space A B`, `blend`, `detector`, `sheetTransition`) are a self-contained corner-chart toolkit parametrised by `A`, `B` — general, but consumed only through `WhitneyPairModel` (123 references), whose ambient model is pinned to 6 dimensions in `BigonModel.lean`, so the generality is not usable downstream
- l.1740 `CleanCornerPatch`, l.1782 `CleanStripPatch`, l.2399 `CleanBigonBoundary`: data structures with 10–15 fields each, no docstring, no field docs; a textbook would state these as "an embedded bigon with clean corners" in prose
- l.33 `set_option maxSynthPendingDepth 3`, l.37–40 kitchen-sink `open scoped … Modular … UpperHalfPlane`, l.42 `universe u v` unused; imports `Morse/CircleGluing` (a Whitney file depending on Morse)
- reading stopped after the statement list and the main statements at l.216, 546, 567, 2399; proofs not read
suggestion: extract `exists_clean_crossingChart` + `finite_transverse_intersections` into a documented `Transversality/Crossing.lean`, move the `MorseSurgeryData.beltIntersection*` block to `Morse/`, and rename every `native`/`Native` identifier.

## Lib/Geometry/Manifold/Whitney/EmbeddedArcs.lean  (88 declarations, 3299 lines)
verdict: C (three statements carry `finrank ℝ E = 6` with `Hemisphere.Sphere 2`/`Ambient 3` and belong to the project proof; the remaining arc/strip lemmas are general but undocumented, `native`-named and split across thirteen families)
twin: Milnor, Lectures on the h-cobordism theorem §6 (Whitney lemma preparation, embedded arcs joining intersection points; named in docstring); Whitney's "arcs avoiding a finite set in dimension ≥ 2" (`exists_embedded_connecting_arc_avoiding_finite_dim_two`, l.1527) is Hirsch Ch. 2/Milnor Top. from the diff. viewpoint; Mathlib: none (genuine gap)
findings:
- l.14–20 module docstring is the move receipt listing thirteen families (`SphereNormalCoordinates`, `WhitneyPairModel`, `CleanBigonBoundary`, `ManifoldImmersion`, `ChartMapPerturbation`, `CurveImmersion`, `TransverseCoordinates`, `NativeParametrization`, `StripCoordinates`, `CleanStripPatch`, `ManifoldMorse.MorseSurgeryData`, `FiberRestriction`, `SmallPerturbation`); no `## Main results`
- 0 of 88 declarations carry a docstring
- l.291 `MorseSurgeryData.opposite_beltIntersectionSigns_iff_Whitney_corners`, l.3018 `nonempty_belt_tubularBigon`, l.3050 `exists_belt_tubular_strip_pair`: hypotheses `(hdim : Module.finrank ℝ E = 6) (hindex : finrank NegativeCoordinates = 2)`, `Hemisphere.Sphere 2`, `Hemisphere.Ambient 3`, `StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))` — the project's 6-manifold index-2 belt argument; not library material (→ `Hopf/Proof`)
- l.1466 `exists_short_embedded_arc`, l.1527 `exists_embedded_connecting_arc_avoiding_finite_dim_two` (`2 ≤ finrank G`, any boundaryless `J`), l.1593 `exists_tubular_connecting_arc_avoiding_finite_with_global_zero`, l.1740 `exists_clean_ambient_chart_along_embedded_arc`: correct general statements, textbook content, undocumented; the `_dim_two` suffix names the hypothesis rather than the result (Mathlib: `_of_two_le_finrank`)
- l.1085–1400 `ManifoldImmersion.exists_*_derivative_repair*`, `ChartMapPerturbation.*`, `CurveImmersion.*`: immersion-repair perturbation lemmas (Hirsch Ch. 2 approximation), a fourth topic; l.3156–3210 `FiberRestriction.*` and l.3211–3299 `SmallPerturbation.composeFamily*` two more
- l.1848 `NativeParametrization.line`, l.2168 `exists_native_clean_strip_matching_germs`, l.2801 `exists_native_shared_corner_strip_pair_dim_two`: "native" project vocabulary
- l.401–540 `WhitneyPairModel.innerBigonMap/innerBigonDiffeomorph/innerBigonCollar`: tied to the 6-dimensional `WhitneyPairModel.Space` of `BigonModel.lean`
- l.33 `set_option maxSynthPendingDepth 3`, l.37–40 kitchen-sink `open scoped … Modular … UpperHalfPlane`, l.42 `universe u v` unused
- reading stopped after the statement list and the statements at l.291, 1527, 2801, 3018–3054; proofs not read
suggestion: move the three `finrank ℝ E = 6` belt statements to `Hopf/Proof`, and regroup the rest into `Whitney/Arcs.lean` (embedded arcs avoiding finite sets, documented) and `Whitney/StripPairs.lean`, dropping `native` from every name.

# done 14 files

## Lib/Geometry/Manifold/Whitney/FrameField.lean  (121 declarations, 2548 lines)
verdict: C (project residue in the mathematics: rank-three specialisation, verbatim stock move, no docstrings)
twin: Milnor, Lectures on the h-cobordism theorem §§5–6 (Whitney trick, named in docstring); no Mathlib twin (genuine gap for the frame-field/complement lemmas)
findings:
- l.15–19 module docstring says "Moved verbatim from the project stock file `Hopf/SingularHomology.lean`" and that declarations "keep their historical dotted names and their order"; no `## Main results`, no statement of the theorem the file proves
- 121/121 declarations without docstring
- l.1357–1815, l.2248–2400 `rankThreePairCoordinates`, `exists_rankThree_*`, `rankThreeSheetPairDet`, `ManifoldMorse.MorseSurgeryData.beltSheetNormal`: the complement/frame arguments (l.455 `exists_smooth_complement_near_starConvex_on`, l.869 `exists_smooth_invertible_join_of_finrank_two`) are general, but the later half hard-codes normal rank 3 and the project's `MorseSurgeryData`; Milnor's argument is for any `k+l = n ≥ 5`
- l.46–70 `WhitneyPairModel.lowerBoundaryArc`/`upperBoundaryArc` and l.261–360 `PlanarFrame.area/quarterTurn/determinant`: ad-hoc 2×2 linear algebra on `PlaneImmersion.Plane` that duplicates `Matrix.det_fin_two`/`LinearMap.det`
- file mixes six namespaces (`FrameField`, `PlanarFrame`, `IntersectionCoordinates`, `DiskFraming`, `StripNormalData`, `NativeSheetCoordinates`) with no section structure; no Mathlib-style `Foo.bar_of_baz` naming (`det_of_zero_lower_left`, `same_sign_frames_iff_coefficients`)
- l.33 `set_option maxSynthPendingDepth 3`, l.37–40 kitchen-sink `open scoped … Modular UpperHalfPlane`, l.42 `universe u v` unused, `import Mathlib`
suggestion: split the general frame-field/complement lemmas (l.179–1268) into a documented `Whitney/FrameField.lean` and move the rank-three and `MorseSurgeryData` material to the project proof tree, adding docstrings throughout

## Lib/Geometry/Manifold/Whitney/RankThreeModel.lean  (160 declarations, 2860 lines)
verdict: C (project residue in the mathematics: dimension fixed at rank three, verbatim stock move, no docstrings)
twin: Milnor, Lectures on the h-cobordism theorem §6 (Whitney's lemma / cancellation of intersection points); no Mathlib twin (genuine gap)
findings:
- l.12–19 module docstring is one run-on sentence plus "Moved verbatim from the project stock file `Hopf/SingularHomology.lean`"; no `## Main results`; the seven families are listed by name only
- 160/160 declarations without docstring
- l.427–445 `RankThreeWhitneyModel.Lower/Upper/Space/LowerSheet/UpperSheet` abbrevs fix the model to `ℝ × ℝ × ℝ`-type spaces; l.651, l.1802, l.2401 `TubularBigon.RankThree{TangentAdapted,SheetParametrized,Compatible}Chart` and l.2832 `exists_rankThree_relative_cancellation` are the project's dimension case of Milnor's general Whitney lemma (arbitrary `k + l = n`)
- l.46–420 `WhitneyPairModel.GraphMotion`/`graphStep`/`exists_supported_graph_height`: the planar model isotopy is general and reusable; it sits in the same file as the rank-three charts (two topics)
- l.2617–2660 `SupportedDiffeomorph.image_inter_eq_diff`, `preimage_target_eq_diff_of_relative_removal`, `eventuallyEq_comp_of_fixed_off_closed` are pure set/filter lemmas about `X ≃ X` misplaced in a manifold file
- l.33 `set_option maxSynthPendingDepth 3`, l.37–40 `open scoped … Modular UpperHalfPlane`, l.42 `universe u v` unused, `import Mathlib`
suggestion: keep the planar `WhitneyPairModel.GraphMotion` section as a documented library file and move the `RankThree*` charts and cancellation (l.427–2860) to the project's proof tree until they are stated for general `k + l = n`

## Lib/Topology/Dimension/CubeBoundaryThreeCells.lean  (213 declarations, 2328 lines)
verdict: C (project residue in the mathematics: dimension-3 cell bookkeeping with proof-ledger labels; not library material as written)
twin: cell structure of the subdivided cube boundary (Engelking §1.8, Hurewicz–Wallman Ch. IV); no Mathlib twin
findings:
- l.11–19 module docstring: "Textbook Section 3, Definition 3.1 and coherence expansion, canonical lines 1368–1620. The declarations below follow the reviewed order L0–L4, D1–D3, C01–C22, H2/H1, F1–F3, E0 …" and l.1399 "CD10C-I implements ordinary textbook Lemma 3.4 (I1, lines 1658–1668)": the file is organised by the project's proof ledger; docstrings begin with labels ("I1 representation: …")
- l.23 `lattice N h`, l.125 `vertices`, l.142 `squareGeom h v j k`, l.714 `edgeParamSet`, l.824 `edgeMidpoint`, l.1791 `square_boundary_edges`, l.1967 `edge_common_endpoint_geometry`: mesh combinatorics of `∂[-1,1]³` in `EuclideanSpace ℝ (Fin 3)` with `Fin 3` case splits (`fin_cases i <;> fin_cases j …`, l.1416); nothing is stated for general `n`
- l.1079 `floor_real_bounds`, l.1115 `normalizedFloorInput_bounds`, l.1173 `ordinary_floor_enclosure`: real-arithmetic lemmas about `⌊·⌋` that belong in `Algebra/Order/Floor`, if not already there
- 53 `private` declarations; 0/213 missing docstrings; two `namespace TopologicalSpace.CubeBoundaryThree` blocks (l.10, l.773); reading stopped at the pattern (sampled every sixth statement)
suggestion: move to the project's proof tree (`Hopf/Proof/Dimension`), extracting only the floor lemmas; a library version would be a cubical-complex structure on `∂[-1,1]ⁿ`
