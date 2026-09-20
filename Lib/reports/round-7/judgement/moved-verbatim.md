# Judgement packet: files whose docstring says "moved verbatim" (round-5 stock moves)

Same treatment as the D files where the auditors mark project residue; otherwise rename project vocabulary and split by namespace.

## Lib/Algebra/Module/IntegerPresentation.lean  (23 declarations, 281 lines)
verdict: C (project residue in the mathematics: two topics, `ℤ` where any ring works, provenance residue)
twin: presentations of finitely generated modules and presentation matrices (Milnor, h-cobordism §7 Thm 7.6 as cited; Lang III.7); Mathlib `Module.Presentation` (Mathlib/Algebra/Module/Presentation/Basic.lean) — a general presentation API this file does not use
findings:
- l.56 `IntegerPresentation B r c` (`map : (Fin r → ℤ) →ₗ B` surjective with kernel spanned by `c` columns), `ofEquiv`, `transport`, `adjoin`, `matrix`, `matrix_surjective_of_subsingleton` (l.62–187): a special case of Mathlib's `Module.Presentation` over `ℤ` with `Fin`-indexed generators/relations; the ring `ℤ` is inessential everywhere
- l.26, 209–276 `HomologyTransport.ker_comp_span_singleton`, `exists_split_rank_one_extension`, `integerCoordinateSplit`, `integerEquiv_one_natAbs`, `matrix_sizes_eq_of_bijective`: unrelated split-extension/rank lemmas under a project namespace (`HomologyTransport`); `matrix_sizes_eq_of_bijective` is `LinearEquiv.finrank_eq` in one line
- l.3 `import Mathlib`; no copyright header; l.14–21 "## Provenance … Moved verbatim from `Hopf/SphereTopology.lean` (lane F0b) … lane F10" — project workflow text in the module docstring
- 23 of 23 declarations undocumented
suggestion: rebuild on `Module.Presentation` over a general `R` (or delete in favour of it), move the `HomologyTransport` lemmas to `Hopf/Proof`, and remove the provenance paragraph.

## Lib/AlgebraicTopology/SingularHomology/LocalContributionsNaturality.lean  (7 declarations, 162 lines)
verdict: B (docs only: no docstrings, porting note as module docstring)
twin: naturality of Hatcher §2.2 Mayer–Vietoris under maps of covers (Hatcher p. 150, "the MV sequence is natural"); Mathlib: none
findings:
- 7 of 7 declarations lack docstrings (`homologyEquiv_symm_single`, `componentMap`, `overlapMap`, `homologyEquiv_map`, `componentConnecting_enlarge`)
- l.28–30 module docstring ends with "Moved verbatim from `Hopf/Recognition.lean` (… qualifier retarget `PeriodTorusHigherHomology.singularHomologyMap_{comp,id} -> …`)": porting history, not documentation; no reference given
- l.109 `componentConnecting_enlarge` (enlarging `U` to `U'` does not change the `i`-component of the localised connecting map) is a natural naturality statement, general in `X`, `ι`; universe 0, `[Fintype ι] [DecidableEq ι]`
- the file is 162 lines continuing `LocalContributions.lean`; Mathlib would merge it there
- l.6 plain `import Mathlib` (siblings use `module`/`public import`); l.33–42 preamble residue (`set_option`, kitchen-sink `open scoped`, `universe u v`)
suggestion: merge into `LocalContributions.lean` with docstrings and delete the "moved verbatim" paragraph.

## Lib/Geometry/Manifold/Morse/AdaptedWindows.lean  (17 declarations, 622 lines)
verdict: C (proof-step lemmas for the project's surgery system; docstring describes a different file; no docstrings)
twin: Milnor, Lectures on the h-cobordism theorem, §4 (Thm 4.1 rearrangement, Thm 4.8 self-indexing) for l.581 `exists_ordered_index_cut`; the rest (level transport of attaching circles for an `AdaptedWindows E f` system) has no textbook counterpart; no Mathlib twin
findings:
- l.56–63 module docstring lists as main results `AdaptedWindows.exists_embedded_level_transport`, `exists_middle_block_realization`, `exists_ordered_middle_family`; none is in this file — all three live in Morse/SurgeryCollapse.lean (l.238, l.891, l.5392); the docstring was written for the pre-split file ("Moved verbatim from `Hopf/SphereTopology.lean`", l.65)
- 0 of 17 declarations have a docstring
- l.7–55 imports 49 Lib files (singular homology, Mayer–Vietoris, suspension, `SimplyConnectedSphere`, `Whitney.BigonModel`, `OrderedCancellation`, …) for a 622-line file whose statements use only Morse/flow vocabulary: the import list is the old stock file's, not this file's
- l.82 `FlowSuspension.exists_relative_regular_level_isotopy_realization` is the one general statement (a supported relative isotopy of a regular level is realised by a flow) — it belongs with the flow/collar theory of Flow/HeightTranslating, under a namespace that is not `FlowSuspension`
- l.180–560 `attachingSphere_reaches_lower_cut`, `backward_basin_reaches_attaching_level`, `exists_same_flow_windows_avoiding_level`, `reaches_old_lower_of_belt_avoidance`, `no_connection_of_upper_index_zero`, …: each is a step of the surgery-window argument stated for `S : AdaptedWindows E f` with `MorseCancellation.nativeMorseIndex`; the general core ("no gradient connection from an index-0 point upward") is textbook but is not isolated
- l.581 `exists_ordered_index_cut`: given self-indexing order, a regular value separating indices `≤ k` from `≥ k+1` — general, textbook (Milnor Thm 4.8 corollary), should be stated for `IsMorse` + `Finite criticalPoints` without `S : AdaptedWindows`
- l.6 `import Mathlib`, l.66–80 `set_option maxSynthPendingDepth`, kitchen-sink `open scoped … UpperHalfPlane`, unused `universe u v`; non-`module` file
suggestion: rewrite the module docstring for the 17 declarations actually present, cut the import list to what is used, and extract l.82 and l.581 as documented general lemmas

## Lib/Geometry/Manifold/Morse/CircleGluing.lean  (56 declarations, 1315 lines)
verdict: C (transit container "moved verbatim" from the stock file: seven families, proof-step lemmas, no docstrings; the `CircleGluing` core is general)
twin: Milnor, Lectures on the h-cobordism theorem, §§5–6 (named in docstring, no theorem number); docstring says "No Mathlib counterpart exists" — true for the surgery rows; for `CircleGluing.periodicCircle` the nearest Mathlib is `AddCircle`/`Circle.exp` (Analysis/SpecialFunctions/Complex/Circle) and `Periodic`
findings:
- l.14–18 module docstring: "Moved verbatim from the project stock file `Hopf/SingularHomology.lean` … The declarations keep their historical dotted names and their order"; seven families (`CircleGluing`, `MorseCancellation`, `ManifoldImmersion`, `NativeOpenSubmanifold`, `AdaptedWindows`, `FlowSuspension`, `ManifoldMorse.MorseSurgeryData`) in one file — not a library module
- 0 of 56 declarations have a docstring
- l.454–890 `CircleGluing.periodicExtension`, `joinedArc`, `joinedLoop`, `circleExp_localDiffeomorph`, `periodicCircle` (+ `_injOn`, `_contMDiff`, `_derivative_injective`): a self-contained, general construction "two embedded arcs with matching endpoint germs glue to an embedded smooth circle in `N`" — the one textbook-grade block; it should be its own documented file (`Geometry/Manifold/Curve/CircleGluing.lean`) stated via `AddCircle`/`Circle`
- l.77–450 `MorseCancellation.exists_native_open_curve_with_germ`, `exists_embedded_return_arc_inside_open`, `exists_disjoint_embedded_return_arc` and l.285–380 `ManifoldImmersion.exists_relative_embedded_avoidance_in_open*`: continuations of Immersion/Relative.lean's avoidance lemmas, split across two files by history rather than subject
- l.1028 `MorseCancellation.unitSphere_eq_two_points_of_finrank_one` is a linear-algebra fact (`sphere 0 1 = {v, -v}` in a 1-dimensional space) in a Morse namespace; l.893 `NativeOpenSubmanifold.injective_mfderiv_subtype_val` is a general open-submanifold lemma
- l.983–1290 `dense_section_of_flow_cylinder`, `AdaptedWindows.exists_orbit_bandBridge`, `FlowSuspension.exists_unique_connection_of_unit_level_count`, `MorseSurgeryData.bijective_beltNormal_comp_of_transverse`: steps of the project's belt-sphere argument with no isolated textbook statement
- l.6 `import Mathlib`, l.28–44 `set_option maxSynthPendingDepth`, kitchen-sink `open scoped … UpperHalfPlane`, unused `universe u v`; non-`module` file
- read: module docstring and all 56 statement heads; proofs not read
suggestion: extract l.454–890 into a documented `CircleGluing` file and merge the rest into their subject files (Immersion/Relative, the surgery-window file) or `Hopf/Proof`

## Lib/Geometry/Manifold/Morse/RearrangementAmbient.lean  (35 declarations, 772 lines)
verdict: C (project residue in the mathematics: two unrelated subjects — ambient transversality patches and the combinatorial inversion counter — and an ad-hoc `sheetSum` disjoint union; docstring says "Moved verbatim from `Hopf/SphereTopology.lean`")
twin: Milnor, h-cobordism §4 proof of Thm 4.8 (reordering by counting inversions) for l.607–772; Hirsch, Differential Topology Ch. 3 (general position by isotopy) for l.82–430; no Mathlib twin
findings:
- l.14–24 module docstring: inventory plus migration receipt (`base 304a0fea`, `spheretop-moves.md`); no theorem statement, no reference
- 30 of 35 declarations without docstrings (`exists_ambient_patch_in_open` l.135, `sheetSum` l.444, `upperValueRank` l.607, `finiteIndexDisorder` l.610, `finiteIndexDisorder_swap_lt` l.690, …)
- l.444 `def sheetSum (X : Type) : ℕ → Type | 0 => PEmpty | n+1 => X ⊕ sheetSum X n` with six hand-rolled instances (l.448–490, `sheetSumTopology`, `sheetSumIsManifold`, …): Mathlib would take `Fin n × X` (or `Σ i : Fin n, X`) and get every instance for free; the section is over `Type` (universe 0), the rest over `Type*`
- l.607–772 `upperValueRank h x = #{y | h x < h y}`, `finiteIndexDisorder h w = Σ w x · upperValueRank h x`, `finiteIndexDisorder_swap_lt`, `exists_adjacent_index_inversion`: the inversion-count induction of Milnor Thm 4.8, pure finite combinatorics, correctly generic in `X`; misplaced in a manifold file and undocumented
- l.82–430 `exists_radius_supported_bump_preparation`, `exists_relative_ambient_patch_step`, `compose_supported_ambient_isotopies` (a `def` returning an existential? l.259), `exists_supported_ambient_disjoint_fixing_closed`: general-position by supported ambient isotopy with 9–10 type parameters `{D Z G H H' K X Y N}`; textbook content but no docstrings and no statement of what "patch" means
- l.69 `set_option maxSynthPendingDepth 3`, l.72–76 `open scoped … Modular UpperHalfPlane`, l.78 `universe u v` unused
- read all statements; proofs not read
suggestion: split: l.607–772 to `Lib/Combinatorics/IndexDisorder.lean` (docstring: Milnor Thm 4.8 inversion count) and l.82–430 into `Transversality/AmbientIsotopy.lean`; replace `sheetSum X n` by `Fin n × X`.

## Lib/Geometry/Manifold/Whitney/AnnularExtension.lean  (60 declarations, 794 lines)
verdict: C (five unrelated families in one file, `TubularBigon` with a default codimension `n := 4` and `circle_nullhomotopies` hypotheses are project residue; zero docstrings; general sphere-nullhomotopy results buried inside)
twin: Milnor, Lectures on the h-cobordism theorem §§5–6 (named in docstring); the sphere-map results `sphereMap_nullhomotopic_of_omitted_point` (l.543), `sphereMap_nullhomotopic_of_dim_lt` (l.554), `sphere_sphere_nullhomotopic` (l.569) are Hatcher §4.1 / Milnor "Topology from the differentiable viewpoint" §7 (`π_m(S^n) = 0` for `m < n`); Mathlib: none (genuine gap; nearest `Mathlib/Topology/Homotopy/HomotopyGroup`)
findings:
- l.14–20 module docstring is a move receipt ("Moved verbatim from the project stock file `Hopf/SingularHomology.lean` … keep their historical dotted names"); it lists five families (`SphereCone`, `AnnularExtension`, `ClosedHemisphere`, `WhitneyPairModel`, `TubularBigon`) and says "the file order is the dependency order" — an admission that the file has no single subject
- 0 of 60 declarations carry a docstring
- l.412 `abbrev UnitSphere E := Metric.sphere (0:E) 1`, l.419 `abbrev Sphere n := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`: root-namespace aliases of Mathlib's sphere (a third spelling after `Hemisphere.Sphere` in `Morse/SurgeryWindows.lean` and Mathlib's own); they pollute the root namespace
- l.543–573 `sphereMap_nullhomotopic_of_omitted_point`, `sphereMap_nullhomotopic_of_dim_lt`, `sphere_sphere_nullhomotopic`: correct, general, textbook statements (root namespace, no docstring) — the file's only upstreamable content, and it is not mentioned in the docstring's title
- l.574, 695, 741 `*_of_circle_nullhomotopies`: hypothesis "every map `S¹ → M` is nullhomotopic" is `SimplyConnectedSpace M` (same finding as `Morse/SurgeryWindows.lean`)
- l.768 `structure TubularBigon … (h : ℝ) (n : ℕ := 4)`: default codimension 4 and `EuclideanSpace ℝ (Fin n)` normal fibre are the project's 6-manifold Whitney disc (2 + 4 = 6); the textbook Whitney lemma is for any `n ≥ 5` with sheets of complementary dimension
- l.46–170 `SphereCone.*` (cone on a sphere as quotient of the closed ball) and l.170–410 `AnnularExtension.clamp/exteriorVector/exists_continuous_annular_extension` are general topology of balls in a normed space; they belong under `Topology/`, not `Geometry/Manifold/Whitney/`
- l.33 `set_option maxSynthPendingDepth 3`, l.37–40 kitchen-sink `open scoped … Modular … UpperHalfPlane`, l.42 `universe u v` unused
suggestion: split out `SphereCone`+`AnnularExtension` (→ Topology) and the three sphere-nullhomotopy theorems (→ AlgebraicTopology, documented, replacing `Sphere n` by Mathlib's sphere), and keep only the bigon-neighbourhood extension and `TubularBigon` here with the codimension as an explicit parameter.

## Lib/LinearAlgebra/Matrix/TransvectionReduction.lean  (10 declarations, 216 lines)
verdict: C (project residue: `MorseCancellation.*` namespace, verbatim stock move, 9/10 undocumented)
twin: Milnor, Lectures on the h-cobordism theorem §7 (algebra of Thm 7.6: a unimodular row is column-reducible to one containing `±1`); Mathlib/LinearAlgebra/Matrix/Transvection.lean (`Matrix.transvection`, `Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal`)
findings:
- l.11–16 "## Provenance: Moved verbatim from `Hopf/Recognition.lean` (lane F0a). The declarations keep their `MorseCancellation.*` names … the upstream-shaped rename to `Matrix.*` is a separate commit" — the file documents its own residue
- l.22–205 every declaration is `MorseCancellation.*` (project vocabulary for `ℤ`-matrix lemmas); `classCoordinateMatrix B v` (l.22) is `LinearMap.toMatrix`-style coordinate matrix under a nonstandard name; `{A : Type}` (l.22, 164, 187) pins universe 0
- l.87 `primitive_row_has_unit_after_column_additions` is the mathematical content (Euclidean reduction of a unimodular `1×n` row); its statement via `List (Fin n × Fin n × ℤ)` of operations mirrors Mathlib's `Pivot` machinery but is not connected to it
- l.164, l.187, l.201 `functional_class_row_surjective`, `transported_classes_of_matrix_product`, `functional_rows_of_matrix_product`: transport lemmas shaped for one consumer, no textbook counterpart
- 9/10 missing docstrings; `import Mathlib`
suggestion: rename to `Matrix.*`, generalise `Type` to `Type*`, document each lemma, and re-derive the row reduction from Mathlib's `Matrix.Pivot`/Smith-form API where possible
