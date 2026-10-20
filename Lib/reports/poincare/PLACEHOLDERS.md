# Poincaré duality seat: placeholder register

Placeholders are hypotheses in the type (structures), never axioms. Every entry names the Lean
hypothesis, where it is consumed, what it says, and what is missing to discharge it.

## P-1 `PoincareDuality.IsPoincareDuality hn μ` — Poincaré duality for closed oriented manifolds

* **Where.** `Lib/AlgebraicTopology/SingularHomology/Orientation/DualityConsequences.lean`.
* **Statement.** For a closed oriented `n`-manifold (`[ChartedSpace (EuclideanSpace ℝ (Fin n)) M]`,
  `[T2Space M]`, `[CompactSpace M]`, `hn : 2 ≤ n`, `μ : Orientation M n`):
  `bijective : ∀ k l (h : k + l = n), Function.Bijective (absoluteDualityMap hn μ k l h)`,
  where `absoluteDualityMap hn μ k l h : SingularCohomology M k →+ SingularHomology M l` is
  `φ ↦ [M] ⌢ φ` (`DualityMap.lean`, proved, no placeholder).
* **Consumed by.** `IsPoincareDuality.cohomologyEquiv`, `.cohomology_top_equiv_int`
  (`H^n(M) ≅ ℤ`), `.homology_isTorsionFree`, `.cohomology_isTorsionFree_of_dim_four` (consumer
  (a) in generic form).
* **Proved towards it.** The Euclidean base case `dualityMap_closedBall_bijective`
  (`EuclideanDuality.lean`): for every orientation of `ℝ^{m+2}` and every closed ball `K`,
  `D_K : H^k(ℝ^{m+2}, ℝ^{m+2} ∖ K) → H_{m+2-k}(ℝ^{m+2})` is bijective; the duality maps and their
  compatibility with restriction (`DualityMap.lean`); relative cohomology with excision and
  Mayer–Vietoris (`SingularCochains/Relative.lean`, `RelativeMayerVietoris.lean`); the relative cap
  product (`CapProduct/Relative.lean`).
* **Missing (Hatcher 3.35/3.36, textbook nodes N18–N22).** (i) *Done* (`CompactSupport.lean`):
  compactly supported cohomology `CompactlySupportedCohomology M k = colim_K H^k(M, M ∖ K)` as a
  direct limit over `Compacts M` and the limit duality map
  `limitDualityMap : H^k_c(M) →+ H_{n-k}(M)` with `limitDualityMap_ofCompact` and
  `limitDualityMap_of_univ` (closed `M`: the component at `K = M` is `absoluteDualityMap`). What is
  missing is the same construction for the open subsets `U ⊆ M` (as subtypes, with the orientation
  restricted) and the identification `H^k_c(U) → H^k_c(M)` for `U ⊆ M` open. (ii) Lemma 3.36: the Mayer–Vietoris ladder
  `H^k_c(U ∩ V) → H^k_c(U) ⊕ H^k_c(V) → H^k_c(U ∪ V) → H^{k+1}_c(U ∩ V)` over
  `H_{n-k}(U ∩ V) → … → H_{n-k-1}(U ∩ V)` commutes up to the sign `(-1)^k` (the relative
  cohomology Mayer–Vietoris sequence is proved, its middle term still as the dual of the biproduct;
  the sign computation at the connecting homomorphisms is the content). (iii) The five lemma
  (Mathlib) and the three inductions: finite unions of convex open subsets of `ℝⁿ`, nested unions
  (homology and `H_c` commute with directed unions, by compact supports), and the finite chart
  induction for closed `M` (charts are open subsets of `M` homeomorphic to open subsets of `ℝⁿ`;
  transport of duality maps along homeomorphisms). (iv) Reduction of the base case from closed
  balls to arbitrary compact subsets of a convex open set (cofinality of balls in the direct
  limit).
* **Not a placeholder, but hypotheses the consumer supplies** (as in M2): `CompactSpace`, `T2Space`,
  the `ChartedSpace` instance of the smooth structure, an `Orientation M n` (for `T⁴/C_m`:
  orientability of the quotient), `PathConnectedSpace`, finite generation of `H_q(M; ℤ)`
  (`Module.Finite ℤ (SingularHomology M q)`, true for closed manifolds but not in `Lib`), and
  torsion-freeness of `H_1(M; ℤ)`.

## Open items that are not placeholders (no Lean hypothesis introduced)

* Dimensions `n = 0, 1` of the orientation theory (M1/M2 assume `2 ≤ n`).
* Non-orientable half of Theorem 3.26.
* Consumer (b), unimodularity of the intersection form (Prop. 3.38): the cup product on
  cohomology and the identity `⟨φ ∪ ψ, [M]⟩ = ⟨ψ, [M] ⌢ φ⟩` are proved
  (`CapProduct/Cup.lean`, `Orientation/IntersectionForm.lean`); that the adjoint
  `H^k(M) → Hom(H^{n-k}(M), ℤ)` is an isomorphism on the free parts needs P-1 (duality) together
  with the universal coefficient isomorphism `H^{n-k} ≅ Hom(H_{n-k}, ℤ)` (proved when `H_{n-k-1}`
  is projective) and the reflexivity of finitely generated free `ℤ`-modules.
* The Ext half of the universal coefficient theorem (torsion of `H^q` ≅ torsion of `H_{q-1}`); the
  torsion dictionary of consumer (a) is proved without it, from the free half and finite generation.
