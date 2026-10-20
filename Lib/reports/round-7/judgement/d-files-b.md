# Judgement packet: D files, part b

For each file: the auditors name the general declarations worth keeping; keep those in Lib (renamed to standard names), move the rest back under Hopf/Proof/<path>.lean with its consumers rerouted; envdiff shows moves only.

## Lib/Algebra/Group/LatticeImageCollapse.lean  (14 declarations, 166 lines)
verdict: D (not library material: the project's explicit monodromy data)
twin: none: this is a computation with the project's two 4×4 integer matrices; no textbook statement
findings:
- l.35–49 `A1`, `A2`, `epsilon`, `epsilonPrime`, `gamma` are the project's explicit integer monodromy matrices and fixed vectors (`![1,2,-4,0]`, `![1,3,-3,0]`); every theorem is about these constants
- l.51 `image_eq_one_of_gamma_eq_zero`, l.79 `image_eq_zpow_gamma`: hypotheses `x * φ v * x⁻¹ = φ (A1 *ᵥ v)` are the project's conjugation relations; conclusions are `decide`-driven facts about `Fin 4 → ℤ`
- 6 of 9 theorems without docstring (l.51, 79, 108, 121, 136, 150); module docstring names no reference and describes proof steps ("kills w and d") rather than a result
- l.13 title "cusp kernel and two matrix actions" and namespace `LatticeImageCollapse` are project vocabulary
suggestion: move the file under `Hopf/Proof` (Center/Threefold computation); if anything is kept in `Lib`, it is only a generic "image of `ℤⁿ` lies in `zpowers c` when a character kernel is killed" lemma with `A1`, `epsilon` as variables.

## Lib/Algebra/Group/ResidualRelations.lean  (1 declarations, 46 lines)
verdict: D (not library material: proof-specific relation elimination)
twin: none: a one-off group-word computation (`x*y=1`, `x^3=d`, `y^4=d⁻¹` ⇒ all trivial)
findings:
- l.27 `ResidualRelations.eq_one_of_mul_eq_one_cube_fourth`: generic `[Group H]`, but the exponents 3 and 4 are the project's residual relations for the `Center` triviality step; there is no textbook statement with these specific relations
- l.17, l.26 docstrings cite `CENTER_NATIVE_TRIVIALITY_TEXTBOOK.md`, "reviewed NT1"
- namespace `ResidualRelations` names no mathematical object; 0 missing docstrings
suggestion: move to `Hopf/Proof` next to the Center triviality argument; the reusable content (`x^m = x^(m+1) → x = 1`) is `pow_eq_pow_iff`/`mul_left_cancel` already in Mathlib.

## Lib/Algebra/Group/SurjectiveDescent.lean  (3 declarations, 53 lines)
verdict: D (Mathlib already has it: `MonoidHom.liftOfSurjective`)
twin: Mathlib `MonoidHom.liftOfSurjective` / `MonoidHom.liftOfRightInverse` (+ `_comp`) in Mathlib/Algebra/Group/Subgroup/Basic.lean l.932; universal property of quotients (Lang, Algebra I §3)
findings:
- l.21 `descendHomOfSurjective f hf g hfg` is `f.liftOfSurjective hf ⟨g, hker⟩` with `Classical.choose` instead of `surjInv`; l.47 `descendHomOfSurjective_comp` is `liftOfRightInverse_comp`
- l.35 `fibre_constant_of_ker_le` converts `f.ker ≤ g.ker` to the fibre condition, i.e. the direction Mathlib's subtype already packages; a Mathlib-style statement would be an `iff`
- l.13 docstring: "strict helper is independent of the Hopf development … overlap character descends across a surjective filling map" — project vocabulary (overlap character, filling map)
- top-level names (no namespace); Mathlib would put them under `MonoidHom`; 0 missing docstrings
suggestion: delete and use `MonoidHom.liftOfSurjective` at the call sites (with `fibre_constant_of_ker_le` replaced by the `f.ker ≤ g.ker` hypothesis directly).

## Lib/Algebra/Homology/ThreeColumnPage/LowerTransfer.lean  (5 declarations, 89 lines)
verdict: D (not library material: the paper's "lower transfer condition")
twin: none: a project-specific conjunction (`d₀`, `d₁` bijective, `d₂ ≠ 0`) and its reformulations
findings:
- l.36 `LowerTransferCondition` is documented as "the paper-facing lower transfer condition" — the condition of the project's paper, not a mathematical notion
- l.46–81 four `lowerTransferCondition_iff_*` equivalences (coefficients are units, over a domain injective, ⇔ `FilteredAbutment` vanishing) are correct but only reformulate that condition
- generic `[CommRing R]`; all documented; no reference
suggestion: move to `Hopf/Proof` next to the theorem that consumes it.

## Lib/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean  (1 declarations, 42 lines)
verdict: D (not library material: a `Finset.induction_on` wrapper for the project's star-attachment induction)
twin: Mathlib `Finset.induction_on` (Mathlib/Data/Finset/Insert.lean) — the theorem is that lemma with a dependent predicate
findings:
- l.29 `exists_stageCharacter (Basepoint : Finset ι → Type*) (Character : ∀ s, Basepoint s → Prop) …`: a five-line induction with abstract `attach` step; nothing about fundamental groups, van Kampen, or characters occurs in the statement
- docstring l.13–17: "used by a star-attachment argument … this owner contains no chart, centre-family, puncture, or residual-group data" — describes the project's proof, in the project's vocabulary
- placed under `FundamentalGroup.VanKampen` although it imports only `Finset.Basic`
suggestion: inline at the call site in `Hopf/Proof` as `Finset.induction_on`.

## Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean  (21 declarations, 174 lines)
verdict: D (n = 6 instantiation of general theorems, moved from `Hopf/Recognition.lean`)
twin: none: every declaration is `Hurewicz.hurewiczLinearEquiv`/`cubeChain_natural` at `m = 3, 4` (as the docstring l.27 says)
findings:
- l.51–170 `SixthHurewicz.*`: 21 declarations that are literally `Hurewicz.foo (m := 4)` (e.g. l.112 `hurewiczLinearEquiv`, l.120 `hurewiczPi6Equiv`, l.163 `hurewiczLinearEquiv_natural`); the degree `6` is the project's `S⁶` dimension; no textbook states a degree-six Hurewicz theorem
- l.33 docstring: "Moved verbatim from `Hopf/Recognition.lean`", i.e. project material by its own account; the `HigherHurewicz → Hurewicz` retargeting note is changelog, not documentation
- 21 of 21 declarations lack docstrings; l.6 `import Mathlib` plus nine Lib imports; l.42–45 kitchen-sink `open scoped ... Modular ... UpperHalfPlane`; l.47 `universe u v` unused; l.38 `set_option maxSynthPendingDepth 3`
suggestion: move the file to `Hopf/Proof/` (or delete it and let the consumer write `Hurewicz.hurewiczLinearEquivOfTwoLE x 6`), replacing it in Lib by nothing

## Lib/AlgebraicTopology/Hurewicz/SphereGenerator.lean  (3 declarations, 132 lines)
verdict: D (degree-six instance for the project's `S⁶` argument; belongs under `Hopf/Proof`)
twin: none: the general statement is Hatcher Thm 4.32 + naturality (already in `HopfDegree.lean`/`Naturality.lean`); this file is its `n = 6` instance
findings:
- l.40 `homotopyMap_bijective_of_homologyMap_bijective` and l.83 `exists_sphereMap_of_homologySixEquiv` quantify `hpi : ∀ k, 2 ≤ k → k < 6 → …` and `SingularHomology X 6 ≃ₗ[ℤ] ℤ`: the degree `6` is hard-coded although every step (Hurewicz naturality, sphere homology, Noetherian surjective-implies-injective) is degree-free; the general form would be a two-line corollary in `HopfDegree.lean`
- l.6 imports `DegreeSix.lean` (verdict D) and uses `SixthHurewicz.homotopyMap`; namespace `SixthHurewicz`
- l.9–28 module docstring is a prose proof sketch with no `## Main results`/`## References` sections, no Hatcher citation, and ends with the disclaimer "No smooth structure, homotopy inverse, or sphere recognition is asserted", which addresses the project's reviewers, not a library reader
- l.30–31 `set_option warningAsError true`, `set_option autoImplicit false` are project-CI options in a library file; 0 missing docstrings (awk hit l.18 is prose)
suggestion: state `exists_sphereMap_of_homologyEquiv` for general `n ≥ 2` next to `HopfDegree.sphere_homotopicRel_of_topClass_eq` and move this file to `Hopf/Proof/`

## Lib/AlgebraicTopology/SingularHomology/LocalDegreeNeighborhoods.lean  (65 declarations, 777 lines)
verdict: D (proof-specific: "native" charts/parametrisations, Morse-theory imports, moved verbatim from `Hopf/SphereTopology.lean`)
twin: none found (the neighbourhood bookkeeping around Hatcher Prop 2.30 has no textbook statement)
findings:
- l.6–53 forty-eight `import`s including `Morse.Handle`, `Morse.SurgeryWindows`, `Morse.Cancellation`, `Morse.Reeb`, `WhitneyEmbedding`, `Whitney.BigonModel`, `Transversality.Basic` — none of which a local-degree file needs; the import list is the project's monolith
- l.63–64 module docstring: "Moved verbatim from `Hopf/SphereTopology.lean` (base `304a0fea`); see `Lib/reports/integration-4/spheretop-moves.md`" — the file documents its own porting, not its mathematics; no reference
- l.84, 193, 280–341, 623–716 `exists_native_boundaryData`, `NativeNeighborhood.*`, `NativeParametrization.centered_symm_self`, `NativeChartTransition.*`: "native parametrisation" is the project's chart convention; statements are `∃ L, L = fderiv (f ∘ centered x) 0 ∧ Nonempty (BoundaryData …)` — existence packaging for one downstream proof
- l.357–528 `SeparatedNeighborhoods` (a finite family of disjoint chart balls around finitely many points with `overlap_eq`, `open_cover`): the genuinely general part, but stated with the same native charts
- l.535–541 `SublevelDisk.contractibleSpace`, `homology_subsingleton` and l.547–716 `LinearSphereAction.sphereMap_comp/_trans/_relative/homology_relative_sign` are stray lemmas belonging to `Morse/SublevelSets` and `LinearSphereAction.lean`
- l.745 `identity_center_mo1973_5731`; 65 of 65 declarations lack docstrings; `E F M : Type` universe 0
- l.67–78 preamble residue (`set_option`, kitchen-sink `open scoped`, `universe u v`); plain `import Mathlib`
suggestion: move the file under `Hopf/Proof` (or `W4W1`), keeping only `SeparatedNeighborhoods` and the four `LinearSphereAction.sphereMap_*` lemmas in `Lib` with docstrings.

## Lib/AlgebraicTopology/SingularHomology/OnePointCover.lean  (48 declarations, 515 lines)
verdict: D (a grab-bag moved verbatim from `Hopf/SphereTopology.lean`; embedded-cell attachment, disk isotopies, sphere point transports and chart Jacobian signs in one file with the Morse import monolith)
twin: none found (pieces: Hatcher §2.2 cellular attachment MV; `isPathConnected_sphere`-style transitivity of `SO(n+1)` on `Sⁿ` for `positiveTransport`)
findings:
- l.6–53 forty-eight imports (`Morse.SurgeryWindows`, `Morse.Cancellation`, `Whitney.BigonModel`, …), l.65–66 docstring "Moved verbatim from `Hopf/SphereTopology.lean` (base `304a0fea`); see `Lib/reports/integration-4/spheretop-moves.md`"
- l.82–140 `EmbeddedCellAttachment.oldHomologyEquiv`, `coverRight_formula`; l.152–184 `DiskShrinking.exists_embedded_disk_isotopy*`; l.201–265 `DiskOnePointCollapse.*`, `OnePointCover.oldPatch/finitePatch/overlapRadius := …` (an ad-hoc numeric radius); l.269 `SphereNormalCoordinates.normalDerivative_smul_isInvertible`; l.278–283 `CoverLocalContributions.localMap/connecting_sum`; l.302–501 `SpherePoint.*` (positive transport of sphere points, chart transition derivatives, `instLocal2`, `instLocal3`, `referencePoint`, `referenceNeighborhood`) — seven namespaces, no common theorem
- l.481 `sign_factor_mo1973_5719 {a b c : ℝ} (hb : b ≠ 0)`: an arithmetic lemma with a Mathoverflow-numbered name; l.488–492 `instLocal2`, `instLocal3` are theorems named like instances
- 48 of 48 declarations lack docstrings; plain `import Mathlib`; l.68–79 preamble residue
suggestion: move the file under `Hopf/Proof`; if anything is kept, `SpherePoint.positiveTransport` (l.332–416: `SO(n+2)` acts transitively on `S^{n+1}` by maps of positive determinant) as a standalone documented lemma.

## Lib/Analysis/Real/MeshScale.lean  (1 declarations, 88 lines)
verdict: D (proof-specific: the project's constants h = 2/N, ε = h/9 and five ad-hoc inequalities)
twin: none: no textbook counterpart (Archimedean property `exists_nat_gt`)
findings:
- l.10–11, 17–19 docstring: "the mesh choice and all inequalities (2.2) from the canonical textbook proof, lines 1355--1366": refers to the project's own proof text by line number, not to a textbook
- l.20 `Real.exists_mesh_scale` packs `h = 2/N`, `ε = h/9`, `h < λ/2`, `8ε < h`, `2ε < h`, `h√2 < λ`, `h + 2ε < λ`, `8ε < λ` into one 12-fold conjunction: constants and conjunction order are those of one consumer proof; the mathematical content is `exists_nat_gt` plus `linarith`
- l.33–84 proof comments `(S-01)` … `(S-09)` are step tags from a work plan; namespace `Real` is Mathlib's, so `Real.exists_mesh_scale` would collide with the Mathlib namespace on upstreaming; l.1–7 no copyright header
suggestion: move to `Hopf/Proof` (or the consumer's file) and inline the constants where used

## Lib/Data/Int/SignedResidual.lean  (1 declarations, 17 lines)
verdict: D (proof-specific: one linear-combination identity with the project's constants 3, −4, 12)
twin: none: no textbook counterpart (a `linear_combination`/`omega` one-liner)
findings:
- l.11 `Int.signed_residual_coordinate_zero : 3u = k → −4v = k → u + v = dk → k = 0`: the constants are the project's (the `(12d − 1)k = 0` computation); no general statement (e.g. `a*u = k`, `b*v = k`, `u + v = d*k`, `(a+b) ∤ …`) is extracted
- l.8–10 docstring cites "`CENTER_NATIVE_H5_VANISHING_TEXTBOOK.md`, HV10": a project document, not a textbook; name `signed_residual_coordinate_zero` names no mathematical object; placed in Mathlib's `Int` namespace and directory `Data/Int/`
- l.1–3 no copyright header; `import Mathlib.Tactic.LinearCombination` non-public
suggestion: move to `Hopf/Proof` (inline at the single use site with `linear_combination`)

## Lib/GroupTheory/PresentedGroup/CentralTwist.lean  (20 declarations, 170 lines)
verdict: D (not library material: a single project-specific presented group)
twin: none: the group `⟨c, x, y | c central, xy = cᵃ, x³ = cᵇ, y⁴ = cᵈ⟩` has no textbook name; nearest Mathlib API is Mathlib/GroupTheory/PresentedGroup.lean (`PresentedGroup.toGroup`, `generated_by`)
findings:
- l.9–15 module docstring: "associated with the central twist data of an exceptional gluing … (presentation taken from the project's gluing data)": the object is defined by the project's proof, not by any textbook
- l.39 `twistRelators`, l.46 `TwistGroup a b d`: the exponents `3` and `4` (l.43) are hard-coded from the project's gluing; l.118 `TwistGroup.generated_by_c` shows the group is cyclic on `c`, so the file's content is the computation `x = c^(4a-b-d)`, `y = c^(-3a+b+d)` (l.98, l.108) — a one-off
- l.134–170 `realizationImages`, `realizationHom`, `realizationHom_c/x/y`: the universal property, generic in `G`, but only meaningful for this presentation
- l.7 `import Lib.GroupTheory.SplitExtension` unused by any statement; `import Mathlib`; l.19 `set_option maxSynthPendingDepth 3`; l.21–26 `open scoped … Modular UpperHalfPlane`; l.28 `universe u v` unused; l.32–34 `local infixr ≫ₚ`/`SlashAction.map` notation unused
- 0/20 missing docstrings; top-level names `twistRelators`/`TwistGroup` without a namespace
suggestion: move the file to the project's proof tree (`Hopf/Proof/…`) next to the gluing that produces the presentation; nothing here generalises

## Lib/GroupTheory/SplitExtension.lean  (13 declarations, 152 lines)
verdict: D (not library material: Mathlib already has the statement)
twin: Mathlib/GroupTheory/GroupExtension/Basic.lean `GroupExtension.Splitting.semidirectProductMulEquiv` (the split extension `≃* N ⋊[conjAct] H`); Weibel, Homological Algebra Ex. 6.1 / Robinson, Theory of Groups 10.1 (named in docstring)
findings:
- l.108 `SplitGroupExtension.mulEquiv i p s φ hi hs hex hconj : N ⋊[φ] H ≃* E` is exactly `GroupExtension.Splitting.semidirectProductMulEquiv` with the extension unpacked into eight explicit hypotheses; `Lib/GroupTheory/GroupExtension/Abelianization.lean` (l.39) already uses the Mathlib version, so this file is dead weight
- l.39–150 every statement repeats `{N E H} [Group N] [Group E] [Group H] (i p s φ hi hs hex hconj)`; Mathlib bundles these as `GroupExtension K E Q` + `Splitting`
- l.55 `projection_inclusion`, l.62 `projection_section`: trivial rewrites of `MonoidHom.mem_ker`/`DFunLike.congr_fun` exposed as named lemmas
- l.6 `import Mathlib`; l.19 `set_option maxSynthPendingDepth 3`; l.21–26 `open scoped … Modular UpperHalfPlane`; l.28 `universe u v` unused; l.32–34 `local infixr ≫ₚ`/`SlashAction.map` notation unused; docstring indented with two spaces (l.9–14)
- 0/13 missing docstrings, `SplitGroupExtension.` namespace is fine but not Mathlib's
suggestion: delete the file and replace its uses by `GroupExtension.Splitting.semidirectProductMulEquiv` (plus `Splitting.conjAct`), keeping at most `mulEquiv_inl/inr` if Mathlib lacks those simp lemmas
