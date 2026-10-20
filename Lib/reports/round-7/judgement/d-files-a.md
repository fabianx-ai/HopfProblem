# Judgement packet: D files, part a

For each file: the auditors name the general declarations worth keeping; keep those in Lib (renamed to standard names), move the rest back under Hopf/Proof/<path>.lean with its consumers rerouted; envdiff shows moves only.

## Lib/Geometry/Manifold/Morse/BeltCancellation.lean  (60 declarations, 1730 lines)
verdict: D (proof-specific: dimension 6 / index 2 belt-sphere cancellation for the project's manifold; "moved verbatim from `Hopf/SingularHomology.lean`")
twin: Milnor, Lectures on the h-cobordism theorem, §§5–6 (Thm 5.4 first cancellation, Thm 6.4 second cancellation via the Whitney trick — named in docstring, no theorem numbers); docstring says "No Mathlib counterpart exists" — correct
findings:
- l.47 `MorseSurgeryData.exists_belt_whitney_cancellation_of_opposite_signs` and l.117 `exists_signed_belt_cancellation_step` carry `(hdim : Module.finrank ℝ E = 6) (hindex : finrank NegativeCoordinates = 2)` and `Hemisphere.Sphere 1/2`, `Hemisphere.Ambient 3` (4 statements with `finrank ℝ E = 6`, 42 mentions of `Hemisphere`): Milnor's second cancellation theorem is for any `n ≥ 6`, `2 ≤ λ ≤ n−3`, simply connected level — these are the project's instance, not the theorem
- l.15–19 module docstring: "Moved verbatim from the project stock file … The declarations keep their historical dotted names and their order"; six unrelated families in one file (`MorseSurgeryData`, `AdaptedWindows`, `MorseCancellation`, `RegularLevel`, `PuncturedRadial`, `LocalDegree.BoundaryData`) — the file is a transit container, not a library module
- 0 of 60 declarations have a docstring
- general material buried inside: l.547/571 `RegularLevel.contMDiffWithinAt_iff_inclusion`/`contMDiffOn_iff_inclusion` (smoothness into a regular level via the inclusion — a `ContMDiff` submanifold lemma), l.769 `surjective_coprod_comp_left` (linear algebra), l.1624–1650 `PuncturedRadial.deformation/sphereHomotopyEquiv` (`E \ 0 ≃ₕ S(E)`, Mathlib has `Homeomorph`-level versions in Analysis/InnerProductSpace? not checked) — these should be extracted; the rest belongs under `Hopf/Proof`
- l.280–400 `HandleDomain`, `handleMap`, `coreMap`, `coreUnionHomotopyEquiv`, `coreCellPresentation`: the core-of-a-handle cell presentation is textbook (Milnor Morse Theory Thm 3.2) but stated for the project's `MorseSurgeryData`, not for a general handle
- l.6 `import Mathlib`, l.32–46 `set_option maxSynthPendingDepth`, kitchen-sink `open scoped … UpperHalfPlane`, unused `universe u v`; non-`module` file
- read: module docstring, all 60 statement heads, the statements at l.47, l.117, l.421 in full; stopped there
suggestion: move the file under `Hopf/Proof` (or `W4W1`) and extract the four general lemmas named above into `RegularLevel`/`Topology/Homotopy` files with docstrings

## Lib/Geometry/Manifold/Morse/CutTransport.lean  (59 declarations, 1496 lines)
verdict: D (not library material: docstring says "Moved verbatim from `Hopf/Recognition.lean`"; the statements are the project's index-2/3 cancellation bookkeeping)
twin: Milnor, h-cobordism Thm 7.6/§7 (basis theorem, cut transport) for the idea only; no Mathlib twin
findings:
- l.14–41 module docstring is a bullet inventory plus a migration note ("Moved verbatim from `Hopf/Recognition.lean` … qualifier retarget `PeriodTorusHigherHomology.* -> SingularHomology.*`"); no theorem statement, no textbook reference
- 55 of 59 declarations have no docstring (`levelSublevelMap` l.66, `middleSectionClass` l.140, `canonicalMiddleMatrix` l.185, `equalCutHomologyEquiv` l.207, `exists_sheet_arc_tube_with_normal_change` l.557, …)
- l.66–560 every `M`/`E` is `Type` (universe 0), unlike the `Type*` of neighbouring files; homology maps hardwired to the project's `SingularHomology` in degree `2`/`3` (`regular_sublevel_inclusion_bijective … 2` l.1373)
- l.1436 `consecutive_last_two_first_three`, l.1478 `native_index_excluded_of_count_zero`, l.249 `native_index_order_of_equal_index_exchange`: hypotheses `nativeMorseIndex E f p = 2`, `≠ 3`, `SurgeryWindows E f` — the W4W1 index-2/3 cancellation, not a textbook statement
- l.1375 `ManifoldMorse.MorseSurgeryData.instLocal1 (n : ℕ) : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n+3))) = (n+2)+1)` stated as a `theorem` named `inst…` — a local instance helper leaked as a public declaration
- l.1266 `MorseCancellation.SurgeryWindows.regular_before_first_middle_pivot`: nested namespace mixing two project packages; l.1379–1399 `SupportedDiffeomorph.IsotopicToIdentity.homotopic`, `conjugate_level_isotopy` are general (isotopy ⇒ homotopy) and misfiled here
- l.557–1200 sheet passages / `LongitudinalTubeMotion` / `CenteredSheetPassage`: 25 declarations of Whitney-trick geometry with `mfderiv` determinant computations, unrelated to "cut transport"; second subject
- l.53 `set_option maxSynthPendingDepth 3`, l.56–60 `open scoped … Modular UpperHalfPlane`, l.62 `universe u v` unused
- read all statements; proofs not read (pattern clear by l.560)
suggestion: move the file back under `Hopf/Proof` (or `W4W1`) as is; extract only `SupportedDiffeomorph.IsotopicToIdentity.homotopic`/`comp_homotopic` (l.1379–1399) and `equalCutHomologyEquiv` (l.191–240, docstrings added, `Type*`) into the library.

## Lib/Geometry/Manifold/Morse/MiddleBlocks.lean  (31 declarations, 1497 lines)
verdict: D (not library material: docstring says "Moved verbatim from `Hopf/Recognition.lean`"; all statements are the project's index-2/3 middle-block accounting)
twin: none found (Smale, h-cobordism / Milnor Thm 7.6 area, but no statement here is a textbook one)
findings:
- l.14–46 module docstring: a bullet inventory of 30 names plus a migration note (`PeriodTorusHigherHomology.* -> SingularHomology.*`); "Second batch of stock results" is not a statement
- 29 of 31 declarations lack docstrings (`nativeMorseCount_eq_interval_length` l.62, `nativeMiddleBaseCut` l.280, `nativeMiddleCutSequence` l.285, `exists_relative_surgery_cut_transport` l.622, …)
- l.62–1470 every type is `Type` (universe 0); hypotheses are the project's `AdaptedWindows E f`, `SurgeryWindows`, `nativeMorseIndex … = 3`, `MorseSurgeryData.beltIntersectionCount`
- l.1426 `middle_blocks_complete_of_no_four_five`, l.224 `nativeIndexThreeAttachingSphere_regular`, l.1468 `critical_pair_of_surgery_count_two`: names encode the W4W1 dimension-6 index bookkeeping ("no four five")
- l.766 `same_image_sphere_maps_unit`, l.1221–1250 `LocalDegree.SeparatedNeighborhoods.pointComplementInclusion`/`componentConnecting_singlePoint`: a general topology fact (two sphere maps with the same image) and a local-degree helper, unrelated to the rest
- l.49 `set_option maxSynthPendingDepth 3`, l.52–56 `open scoped … Modular UpperHalfPlane`, l.58 `universe u v` unused
- read all statements; proofs not read (pattern clear at l.300)
suggestion: move back under `Hopf/Proof`/`W4W1`; if anything is kept, only `same_image_sphere_maps_unit` (l.766) after generalising `Y : Type` to `Type*` and adding a docstring.

## Lib/Geometry/Manifold/Morse/MinimalSystem.lean  (4 declarations, 77 lines)
verdict: D (not library material: `SixSphere` is the project's object; the two connectivity lemmas are instances of Mathlib's `ContinuousMap.HomotopyEquiv.simplyConnectedSpace`, the homology one of the project's `unitSphere_homology_subsingleton`)
twin: Mathlib `ContinuousMap.HomotopyEquiv.simplyConnectedSpace` (used verbatim at l.64 as `e.simplyConnectedSpace`) and `EuclideanSphere.simplyConnectedSpace`; Smale 1961 Thm A named in docstring for the downstream use only
findings:
- declaration count: the rubric grep reports 5 because l.24 of the docstring begins with "theorem (Smale 1961, …"; real count 4 (`SixSphere` l.58, three theorems l.61–71)
- l.14–46 docstring is long and honest ("the two-critical-point Morse conclusion is assembled over this data, not inside this file"; "No Mathlib counterpart exists; … no Mathlib file to converge to") — it declares itself hypothesis-generation input, i.e. `Hopf/Proof` material
- l.58 `abbrev SixSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1` at root namespace: project object, `SixSphere` is a rubric-listed residue name
- l.61, 66 `simplyConnectedSpace_of_homotopySixSphere`, `pathConnectedSpace_of_homotopySixSphere`: one-line specialisations of Mathlib `HomotopyEquiv.simplyConnectedSpace` + `EuclideanSphere.simplyConnectedSpace 4` to `n = 7`; l.71 `homotopySixSphere_homology_subsingleton` over `M : Type` (universe 0) with `SingularMayerVietoris.SingularHomology`
- 4 of 4 declarations without docstrings; file name `MinimalSystem` matches nothing in the file (no "minimal", no "system")
- l.50 `set_option maxSynthPendingDepth 3`; no `universe`, preamble otherwise clean
suggestion: delete the file from `Lib/` and inline the three one-liners where they are used under `Hopf/Proof` (or state one general `homotopyEquiv_unitSphere_homology_subsingleton (n k)` in SphereHomology and drop `SixSphere`).

## Lib/Geometry/Manifold/Morse/SurgeryHomology.lean  (80 declarations, 945 lines)
verdict: D (verbatim move from `Hopf/SphereTopology.lean`; docstring names four declarations that live in another file; zero docstrings; the mathematics is ordered-window bookkeeping for the project's index-2/index-3 argument)
twin: Milnor, Lectures on the h-cobordism theorem §4 (self-indexing/ordered Morse functions: `SurgeryWindows.point`, `first_globalMin`, `last_globalMax`, `first_index_zero`, `last_index_dimension`); Hatcher §2.2 for the exact sequences; no Mathlib twin (nearest: `isPathConnected_sphere` used at l.83)
findings:
- l.14–24 module docstring promises `morse_exact_at_lower`, `morseConnectingMap`, `middlePresentation`, `middleMatrix`; none is declared here (all four are in `SurgeryCollapse.lean`) — stale; closes with a move receipt ("Moved verbatim … base `304a0fea`") rather than a reference
- 0 of 80 declarations carry a docstring
- l.385–435 `FiniteSignedCancellation.*` (`sum_sdiff_pair`, `card_eq_natAbs_sum_of_no_opposite`) is pure `Finset`/`SignType` combinatorics; belongs in Algebra/BigOperators, not Morse theory
- l.436–516 `RadialFilling.direction/radialTime/filling` is a radial null-homotopy of a sphere map on `Hemisphere.Sphere n` with hard-coded `1/4`, `3/4` cutoffs (l.465, 470): a Topology helper, not surgery homology
- l.874–935 `indexTwoNormalModel`, `HasIndexTwoPrefix`, `HasIndexThreeBlock`, `indexThreeBoundaryEquiv`: hard-coded indices 2 and 3 are the project's 6-manifold argument (index-2 prefix followed by an index-3 block), no textbook counterpart
- l.83–320 `SurgeryWindows.values/count/point/first/last` and the global min/max lemmas are correct textbook material (Milnor h-cob §4) stated for general `E`, `M`, but 18 statements pin `{E M : Type}` (universe 0) while 51 use `Type*` in the same file
- l.644–715 `MorseHandle.beltCollapseCoordinate` and `hasFDerivAt_*` are chart-level calculus; l.321–384 `FlowConstruction.regularLevelHomeomorphOfFlow` a third topic
- l.70 `set_option maxSynthPendingDepth 3`, l.74–77 kitchen-sink `open scoped … Modular … UpperHalfPlane`, l.79 `universe u v` unused; 55 imports
suggestion: move `FiniteSignedCancellation` and `RadialFilling` out to their own small files, keep `SurgeryWindows.point/first/last/*_globalMin/*_index_*` as a documented `Morse/OrderedWindows.lean`, and send the index-2/3 block predicates to `Hopf/Proof`; rewrite the module docstring to list what is actually declared.
