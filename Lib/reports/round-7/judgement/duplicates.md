# Judgement packet: internal duplicates (AUDIT.md finding 5)

Each item: decide which copy survives (prefer the Mathlib-PR copy, the general-n copy, the documented copy), reroute consumers, delete the other; envdiff must show the lost names as exactly the deleted copy with the surviving name in the receipt.

1. `Lib/AlgebraicTopology/FundamentalGroup/VanKampen.lean` (1,823 lines) vs the `VanKampen/` split (`Basic`, `PathValue`, `Pushout`, `Surjectivity`): port the docstrings and the uniqueness half into the split, delete the monolith.
2. `Lib/AlgebraicTopology/SingularHomology/Chains.lean` vs the Mathlib-PR files `SimplexPaths`, `CycleClasses`, `Degree1` (pre-PR duplicates under `SingularChains.*`).
3. Barycentric subdivision and the mesh estimate: `SingularHomology/MayerVietoris.lean` l.1127–2600 vs `SingularSmallChains/Barycentric/*` (A-grade); also `Coproduct.homologyBiproductEquiv` duplicated there.
4. Mayer–Vietoris naturality proved twice in `SingularHomology/Naturality.lean` (`CoverNaturality.*` vs `SingularMayerVietoris.*`, identical hypotheses).
5. Hatcher Prop 2.6 twice: `Sum.lean` (binary) vs `Coproduct.lean` (finite).
6. `Ext/InjectiveResolutionHomology.lean` vs `Ext/InjectiveResolutionCoyoneda.lean` (same theorem, second encoding; third copy of the `shortCycleClass` helpers).
7. The H¹-first sheaf pipeline (`SingularCochainSheaf/{ComparisonH1,GlobalUnitH1,GlobalUnitH1Criterion,GlobalResolutionH1,LocalExactH1,ResolutionH1,Pullback/ComparisonH1,Pullback/FiniteClosedH1,PrimitivesH1}`) vs the `*Positive` files at n = 0; the ad-hoc Prop predicates (`GlobalUnitSurjective`, `GlobalKernelLocallySmall`, `SmallKernelGlobalOne`, `SmallKernelGlobal`, `HasSmallChainEquivalences`) collapse into one theorem on normal paracompact spaces (`BarycentricSmallChains.lean` proves the last for every space).
8. `Sheaves/FunctionSheaf.lean` vs `DependentFunctionSheaf.lean` (constant-family copy).
9. The constant ℤ sheaf under `unitSheaf`, `constantIntegerSheaf`, `integralSheaf`, `unitFreeTopIso`; the global-sections functor under `globalSectionsFunctor`, `sheafGlobalSectionsFunctor`, `GlobalSections`, `topEvaluation`; `presheafToSheaf` aliased three times.
10. Mesh files `MeshLebesgue`/`MeshAffine`/`MeshSubdivision` superseded by `ArbitraryCoverMesh.lean`; `SingularSmallChains/Basic.lean` degree-one lemmas subsumed by `CochainHomotopy.lean`; the three two-set-cover files.
11. `AcyclicResolutionH1` vs `TwoStepResolution` (two structures for the same four-term exact sequence); the `Ext/PostnikovD2*` cluster stated for column p = 0 while `SpectralObject/PostnikovD2.lean` has the general form.
