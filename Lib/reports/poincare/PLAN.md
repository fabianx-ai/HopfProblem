# Poincaré duality in `Lib`: plan

Seat: Claude Fable 5.1 (`claude-fable-5-1`), work seat, started 2026-10-20. Branch `lib/poincare` from
`lib/integration` at `bf6688c0`, worktree `/home/goblin/hopf-poincare`. Written before the first line of
Lean, as the task asks; revised only in the sections marked "revised".

## 0. Target

Poincaré duality for closed topological manifolds with integer coefficients, in `Lib`'s own singular
(co)homology (`SingularChains.singularComplex`, `SingularMayerVietoris.SingularHomology`,
`AlgebraicTopology.SingularCochains.complex`), as library material with its own placeholder register
(`PLACEHOLDERS.md`, empty until something has to be registered). Consumers that fix what matters
(`Center/reports/native/ITEM-28.md` §P8, `ITEM-30.md` step 2, paper §4 Lemma 4.5):

* (c) `H₆(X; ℤ) ≅ ℤ` for a closed simply connected 6-manifold — needs orientability of simply
  connected manifolds and the fundamental class (milestones 1–2), not duality;
* (a) all `H^q(S; ℤ)` torsion-free for a closed 4-manifold `S` with `H₁` free of rank 2 and `χ = 0` —
  needs duality in every degree plus the UCT torsion dictionary (milestone 4);
* (b) the intersection form on `H²(S)` unimodular — duality plus cup/cap and the Kronecker pairing
  (milestone 4).

## 1. What `Lib` has (census, 2026-10-20)

* Chains: `SingularChains.singularComplex X : ChainComplex (ModuleCat ℤ) ℕ` for `X : Type`, simplices
  `SingularSimplex X n = C(stdSimplex ℝ (Fin (n+1)), X)`, `simplexChain`, `chainBasis`/`chainsEquivFinsupp`,
  `boundary_simplex`, functoriality `singularChainMap`.
* Homology: `SingularMayerVietoris.SingularHomology X n`, `singularHomologyMap`; cycle-level API
  `ModuleHomology.{Cycle, cycleClass, homologyMap_cycleClass, quasiIso_of_cycle_boundary_lifting}`;
  `HomologyLongExact`: the long exact sequence of a `ShortComplex.ShortExact` of chain complexes of
  `ℤ`-modules (`connectingMap`, `exact_at_{left,middle,right}Homology`, `connectingMap_naturality`,
  `connectingMap_homologyClassOfCycle`).
* Subcomplexes: `supportedChainSubmodule U n` (chains with every simplex in `U`), `smallChainSubmodule
  U V n = supported U ⊔ supported V`, `smallComplex U V` with `smallInclusion U V` a quasi-isomorphism
  for open `U, V` covering `X` (`smallInclusion_quasiIso`, Hatcher 2.21), `subtypeInclusion_chain_range`
  (the chains of the subtype `U` map onto `supported U`), `subtypeInclusion_chain_injective`,
  `supportedChainSubmodule_inf`, `inducedChain_mem_supported_of_mapsTo`; the Mayer–Vietoris sequence.
* Homotopy invariance (`SingularHomology.homotopic_homologyMap`, `homotopyEquivHomologyEquiv`,
  `homeomorphHomologyEquiv`, contractible/point vanishing), `H₀` of path-connected spaces
  (`connectedHomologyZeroEquiv`, natural), spheres (`SphereHomology.unitSphereHomologyTopEquiv :
  H_{n+1}(S^{n+1}) ≃ₗ[ℤ] ℤ`, `unitSphere_homology_subsingleton`), the punctured space
  (`PuncturedRadial.sphereHomotopyEquiv : S(E) ≃ₕ {x : E | x ≠ 0}`), suspension, sums.
* Cochains: `AlgebraicTopology.SingularCochains.dualComplex A K` for any `K : ChainComplex (ModuleCat ℤ) ℕ`
  and `A : AddCommGrpCat`, `complex X A`, pullback, homotopy invariance; `DualEvaluation`: the
  Kronecker evaluation `cohomologyEvaluation : H^{m+1}(K; A) → Hom(H_{m+1}(K), A)` with naturality and
  surjectivity for free complexes; on `center/native` (not here) `DualEvaluation/ExtTerm.lean`: the `Ext`
  half of the UCT and the torsion criterion (cherry-pick with `-x` when milestone 4 needs it).
* Not present: relative homology in any form, excision, local homology, orientations, cap or cup
  products, compactly supported cohomology. Mathlib (pinned `db584cd6`, 2026-08-10) has
  `singularChainComplexFunctor`, homotopy invariance, `H₀`; no relative homology, no manifolds'
  orientation (its `ChartedSpace` docstring only mentions orientable manifolds as a groupoid example).
  Mathlib's `IsCoveringMap` has path lifting, homotopy lifting and the lifting criterion
  `IsLocalHomeomorph.existsUnique_continuousMap_lifts` (Topology/Homotopy/Lifting.lean), which is what
  "simply connected ⇒ orientable" needs. Mathlib's `Algebra/FiveLemma.lean` has the four and five
  lemmas for modules.

## 2. Route: Hatcher §3.3, with three adjustments for `Lib`'s framework

The route is Hatcher, *Algebraic Topology*, §3.3: local orientations as generators of
`H_n(M, M ∖ x)`, the orientation covering, Lemma 3.27 (local-to-global), the fundamental class
(Theorem 3.26), the cap product, Theorem 3.30 through the compactly supported form (Hatcher's proof
needs the noncompact statement for the open pieces of the Mayer–Vietoris induction; there is no
closed-manifold-only shortcut in singular homology without triangulations). The adjustments:

1. **Relative homology as a quotient complex inside `Chains X`.** `relativeComplex X A` has degree-`n`
   term `Chains X n ⧸ supportedChainSubmodule A n`; the pair sequence `0 → C(A) → C(X) → C(X, A) → 0` is
   a `ShortComplex.ShortExact` by `subtypeInclusion_chain_{injective,range}`, so `HomologyLongExact`
   gives the long exact sequence at once. For an open `U ⊆ X` the pair `(U, U ∖ K)` is taken on the
   subtype `U` with the set `(↑) ⁻¹' (U ∖ K)`; excision and the relative Mayer–Vietoris sequence are
   proved inside `Chains X` (quotients of `supported U` by `supported A`, second isomorphism theorem on
   submodules) and transported along the chain isomorphism `singularComplex U ≅ supportedComplex U`.
2. **No reduced homology, no cubes, no covering-space continuity in Lemma 3.27.**
   `H_n(E, E ∖ 0) ≅ ℤ` (`E = EuclideanSpace ℝ (Fin n)`) comes from the pair sequence with
   `H_*(E) = 0` in positive degrees and `H_{n-1}(E ∖ 0) ≅ H_{n-1}(S^{n-1})` for `n ≥ 2`, and from the
   `H₀` computation for `n = 1`. The convex comparison (Hatcher's "ℝⁿ ∖ B deformation retracts onto a
   sphere") is one lemma: for a bounded convex `S ∋ x` in a normed space, the inclusion
   `E ∖ S → E ∖ {x}` is a homotopy equivalence (both deformation retract radially from `x` onto a large
   sphere; convexity keeps outward rays outside `S`). It serves open balls, closed balls and compact
   convex sets alike, so Hatcher's cubes are replaced by finitely many closed balls of radius
   `δ/2`, and the class of "finite unions of compact convex sets" (closed under intersection by
   distributivity) carries the induction. The uniqueness half of 3.27(3) uses the openness of
   `{x ∉ C | [z]_x = 0}` directly (the restriction from a ball to a point is an isomorphism), not the
   covering space.
3. **Compactly supported cohomology without `Module.DirectLimit`.** The duality property of an open
   `U` is stated elementwise: the maps `D_K : H^k(U, U ∖ K) → H_{n-k}(U)`, `φ ↦ φ ∩ μ_K` (`μ_K` from
   3.27), are jointly surjective, and `D_K φ = 0` forces `φ ↦ 0` in `H^k(U, U ∖ K')` for some compact
   `K' ⊇ K`. This is exactly "colim D_K is an isomorphism" and is what the Mayer–Vietoris and nested-union
   steps of Hatcher's proof use; it avoids building the direct limit and its exactness. For a closed
   `M` the finite chart induction `U_j = V_1 ∪ … ∪ V_j` replaces Zorn's lemma.

Manifolds: `[TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]`, `M : Type`
(singular chains live in universe 0); closed = `[CompactSpace M]`. No second countability is needed.
Coefficients `ℤ` throughout (the framework is `ℤ`-pinned; the cochain side is `AddCommGrpCat.of ℤ`).

## 3. Milestones, files, acceptance checks, size estimates

Each milestone: green `lake build Lib Lib.AxiomAudit`, probes within the three standard axioms, a
receipt `Lib/reports/poincare/M<k>.md`, `PROGRESS.md` rewritten, small commits. Line estimates are
Lean lines including docstrings.

### M0 — Relative singular homology (new; Hatcher §2.1 relative groups, §2.2 excision) — ~2,500 lines

`Lib/AlgebraicTopology/SingularHomology/Relative/`, namespace `RelativeSingularHomology`:

* `Chains.lean`: `boundary_mem_supported`, `supportedComplex U` (subcomplex, with the chain
  isomorphism `supportedComplexIso U : singularComplex U ≅ supportedComplex U` from the subtype),
  `relativeComplex X A`, `RelativeHomology X A n := (relativeComplex X A).homology n`, `relativeProjection`,
  `pairSequence X A : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)`, `pairSequence_shortExact`,
  `pairConnecting`, `pair_exact_at_*`; `relativeHomologyEquivOfEmpty : RelativeHomology X ∅ n ≃ₗ[ℤ]
  SingularHomology X n`, `relativeHomology_subsingleton_of_univ : Subsingleton (RelativeHomology X univ n)`.
* `Functoriality.lean`: maps of pairs `relativeChainMap (f : C(X, Y)) (hf : MapsTo f A B)`,
  `relativeHomologyMap`, `_id`, `_comp`, naturality of the pair sequence, restriction along
  `A ⊆ A'` (`restrictionMap : RelativeHomology X A n →ₗ[ℤ] RelativeHomology X A' n`, a special case),
  `relativeHomologyMap_bijective_of_bijective` (five lemma: a map of pairs that is a homology
  isomorphism on both spaces is one on the pair), hence `relativeHomologyMap_bijective_of_homotopyEquiv`.
* `Support.lean`: `chainSupport c : Set X` (union of the images of the simplices in the support of
  `chainsRepr c`), `isCompact_chainSupport`, `mem_supported_iff_chainSupport_subset`, relative cycles
  (`relativeCycle`): a class of `RelativeHomology X A n` is represented by `z : Chains X n` with
  `∂z ∈ supported A`, and then represents a class of `RelativeHomology X A' n` for every
  `A' ⊇ chainSupport (∂z)`, compatibly with restriction.
* `Excision.lean`: for open `U, V` with `U ∪ V = univ`, the map of pairs `(V, V ∩ U) → (X, U)` induces
  `excisionEquiv : RelativeHomology V ((↑) ⁻¹' U) n ≃ₗ[ℤ] RelativeHomology X U n` (through
  `smallInclusion_quasiIso`, the five lemma, and the second isomorphism theorem).
* `MayerVietoris.lean`: for open `A, B ⊆ X`, the exact sequence
  `H_n(X, A ∩ B) → H_n(X, A) ⊕ H_n(X, B) → H_n(X, A ∪ B) → H_{n-1}(X, A ∩ B)` (Hatcher's relative
  Mayer–Vietoris for the pairs used by Lemma 3.27).

Acceptance: `excisionEquiv`, `pairConnecting` exactness, `relativeHomologyEquivOfEmpty` build; probes.

### M1 — Local homology and orientations (Hatcher 3.3 up to Prop. 3.25) — ~2,500 lines

`Lib/AlgebraicTopology/SingularHomology/Orientation/`, namespace `ManifoldOrientation`:

* `ConvexComplement.lean`: `complementHomotopyEquiv : (E ∖ S) ≃ₕ (E ∖ {x})` realized by the inclusion,
  for `S` bounded convex, `x ∈ S` (normed `ℝ`-space `E`).
* `LocalHomology.lean`: `localHomology M x n := RelativeHomology M {x}ᶜ n`; for `E = EuclideanSpace ℝ
  (Fin n)`, `n ≥ 1`: `localHomologyEuclideanEquiv : localHomology E x n ≃ₗ[ℤ] ℤ` and
  `localHomologyEuclidean_subsingleton` in other degrees; the ball restriction
  `ballRestriction : RelativeHomology M Bᶜ n →ₗ[ℤ] localHomology M y n` is bijective for `y ∈ B`, `B` a
  chart ball (`B = (chartAt x).symm '' ball`), by excision to the chart and `ConvexComplement`;
  `localHomologyEquiv : localHomology M x n ≃ₗ[ℤ] ℤ` for an `n`-manifold, and vanishing in other degrees.
* `OrientationCover.lean`: the étalé space `LocalHomologyCover M n := Σ x, localHomology M x n` with
  the topology generated by the images of the sections `y ↦ ⟨y, β|_y⟩` (`B` open, `β ∈ H_n(M, M ∖ B)`);
  `isCoveringMap_localHomologyCover`; the sub-cover of generators `OrientationCover M n` (two-sheeted).
* `Orientation.lean`: `IsLocallyConsistent (s : ∀ x, localHomology M x n)`; `Orientation M n` as a
  structure (generators, locally consistent); `IsOrientable`; `continuous_iff_isLocallyConsistent` for
  sections of the cover; `orientation_of_simplyConnected : SimplyConnectedSpace M → Nonempty (Orientation
  M n)` for connected `M` (lift `id` through the orientation cover by
  `IsLocalHomeomorph.existsUnique_continuousMap_lifts`; manifolds are locally path connected).

Acceptance: `localHomologyEquiv`, `isCoveringMap_localHomologyCover`, `orientation_of_simplyConnected`.

### M2 — The fundamental class (Hatcher Lemma 3.27, Theorem 3.26) — ~3,000 lines

`Orientation/FundamentalClass.lean` (+ `Orientation/EuclideanCompact.lean`):

* Lemma 3.27 for `E`: for a finite union `K` of compact convex sets, `H_i(E, E ∖ K) = 0` for `i > n`,
  and every locally consistent section has a unique class over `K` (induction with the relative
  Mayer–Vietoris sequence); then for an arbitrary compact `A ⊆ E` by the closed-ball cover of
  radius `δ/2` and the support of `∂z`.
* Lemma 3.27 for `M`: compact `A ⊆ M` as a finite union of compact pieces in chart domains, excision
  to the chart, transport along the chart homeomorphism, the same union induction.
* Theorem 3.26: for closed `M` with an orientation `μ`, `fundamentalClass μ : SingularHomology M n` is
  the unique class restricting to `μ x` at every `x`; `homology_subsingleton_of_lt :
  Subsingleton (SingularHomology M i)` for `i > n`; for connected closed oriented `M`,
  `restrictionEquiv : SingularHomology M n ≃ₗ[ℤ] localHomology M x n`, hence `≃ₗ[ℤ] ℤ`. Consumer (c).

### M3 — Cap product (Hatcher §3.3 "cap product") — ~2,500 lines

`Lib/AlgebraicTopology/SingularCochains/CapProduct/`: front and back faces of a simplex
(`frontFace k l : Simplex k → Simplex (k + l)`, `backFace`), the chain-level cap
`capChain : (Chains X (k + l) →ₗ[ℤ] ℤ) → Chains X (k + l) →ₗ[ℤ] Chains X l`, the Leibniz formula
`∂(φ ∩ σ) = (-1)^k (δφ ∩ σ - φ ∩ ∂σ)`, the induced `cap : H^k(X) → H_{k+l}(X) →ₗ[ℤ] H_l(X)`, the
relative forms `H^k(X, A) ⊗ H_{k+l}(X, A) → H_l(X)` and `H^k(X) ⊗ H_{k+l}(X, A) → H_l(X, A)`,
naturality `f_*(f^*φ ∩ α) = φ ∩ f_*α`, and the degree-`k = l`-pairing `φ ∩ α = ⟨φ, α⟩ · [pt]`.
Twin for the simplicial combinatorics: `Lib/AlgebraicTopology/SingularHomology/CrossProduct/Chain.lean`.

### M4 — Duality (Hatcher Theorem 3.30, 3.35, Prop. 3.38) — ~6,000 lines, four sub-milestones

* M4a relative cohomology: `dualComplex (AddCommGrpCat.of ℤ) (relativeComplex X A)`, the pair
  sequence (the dual of a short exact sequence of free complexes is short exact), excision for
  cohomology (the dual of a quasi-isomorphism of bounded-below free complexes is one — via the UCT
  naturality of `DualEvaluation` and `ExtTerm`, cherry-picked), the relative cohomology Mayer–Vietoris
  sequence.
* M4b the duality maps `D_K` and their compatibility with restriction and excision; the elementwise
  duality property; the base case of a convex open `B ⊆ E` (`H^k(B, B ∖ K)` for compact convex `K`
  through `localHomologyEuclideanEquiv` and the Kronecker evaluation; `D` an isomorphism by the
  pairing formula of M3).
* M4c Hatcher 3.36 (the Mayer–Vietoris square commutes up to sign) and the two induction steps
  (union of two opens, nested union); open subsets of `E` by the ball induction; closed `M` by the
  finite chart induction. Headline: `poincareDualityEquiv (μ : Orientation M n) (k ≤ n) :
  SingularCohomology M k ≃ₗ[ℤ] SingularHomology M (n - k)`, `φ ↦ φ ∩ fundamentalClass μ`.
* M4d consumers: `H^n(M) ≅ ℤ`, the torsion dictionary with the UCT (`ExtTerm`): torsion of `H^q` ≅
  torsion of `H_{q-1}`, so for a closed oriented 4-manifold with `H₁` free every `H^q` is torsion-free
  (`χ = 0` enters only through the Betti numbers, which the consumer computes); the cup-product
  pairing `H^k ⊗ H^{n-k} → ℤ` as `⟨φ ∪ ψ, [M]⟩ = ⟨φ, ψ ∩ [M]⟩` and its unimodularity on the free parts
  (Prop. 3.38, needs the cup product: a sibling of M3 with the same front/back faces).

### M5 — Smooth bridge — ~200 lines

A smooth manifold is a `ChartedSpace` manifold already; the only extra statement worth recording is
that the model `EuclideanSpace ℝ (Fin n)` with `𝓘(ℝ, E)` is what the center seats have, so
`Orientation`/`fundamentalClass` apply to `X_0` as is; the orientation of `X_0` itself (ITEM-28) is
their work, not `Lib`'s.

## 4. Expectation

Honest estimate for this session, in order: M0 and M1 complete; M2 complete (it is the most intricate
proof but has no open design question); M3 complete if the face combinatorics cooperate; M4 begun
(M4a, M4b) and the rest registered with exact statements. (c) is served by M2; (a) and (b) only by M4.
If a milestone cannot be finished, the register carries the exact missing statement as a hypothesis
structure, never an axiom.

## 5. Checks (per commit / before finishing)

`lake build Lib Lib.AxiomAudit` green, probes ⊆ `propext, Classical.choice, Quot.sound`; before
finishing `lake build Solution S6Shortcuts S6 Challenge`, `lake build Shared Center`,
`python3 scripts/lib_stock_census.py --check` (123), the isolation greps of `NEXT_STEPS.md`.
Guarded wrapper `/home/goblin/.claude/jobs/06995e68/tmp/poincare/lake.sh` (`taskset -c 0-7`).
