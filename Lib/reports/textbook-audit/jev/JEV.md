# Jev (TypeSafe System One, `jev-1.13.0`) against the ten auditors — 2026-09-20

Files compared: 445; input tokens: 1,598,993. Script `classify.py` (state = path, module docstring, preamble, statement heads, counted facts; 7 questions per file), answers `results.jsonl`.

## Verdict letter

- exact agreement: 192/445 = 43%; within one letter: 405/445 = 91%
- at Jev confidence ≥ 0.5 (151 files): exact agreement 82/151 = 54%
- mean of (Jev readiness score − auditor ordinal): -0.39 (0 = same scale; negative = Jev more lenient)

| auditors \ Jev | A | B | C | D |
|---|---:|---:|---:|---:|
| A | 35 | 9 | 1 | 0 |
| B | 120 | 57 | 37 | 1 |
| C | 27 | 34 | 99 | 0 |
| D | 5 | 6 | 13 | 1 |

## Yes/no judgments against keyword labels from the auditors' findings

Labels are keyword matches on the finding lines (approximate). For each judgment: how often the auditors' findings mention it, Jev's mean probability when they do and when they do not, and a threshold-0.5 accuracy.

| judgment | auditors mention it | Jev mean p (mentioned) | Jev mean p (not) | accuracy@0.5 |
|---|---:|---:|---:|---:|
| residue | 88/445 | 0.31 | 0.08 | 85% |
| docs_stale | 68/445 | 0.51 | 0.35 | 76% |
| multi_topic | 80/445 | 0.24 | 0.11 | 83% |
| mathlib_has | 164/445 | 0.23 | 0.20 | 63% |
| pinned | 215/445 | 0.53 | 0.30 | 70% |

## Two-letter disagreements

| file | auditors | Jev | Jev confidence |
|---|---|---|---:|
| `Lib/Topology/Sheaves/SheafificationLocal.lean` | D | A | 0.33 |
| `Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean` | D | A | 0.88 |
| `Lib/CategoryTheory/Sites/Leray/DegreeZero.lean` | D | A | 0.79 |
| `Lib/AlgebraicTopology/FundamentalGroup/VanKampen/FiniteStarCharacter.lean` | D | A | 0.13 |
| `Lib/Algebra/Group/SurjectiveDescent.lean` | D | A | 0.13 |
| `Lib/Topology/Sheaves/StalkwiseSectionRange.lean` | C | A | 0.53 |
| `Lib/Topology/Sheaves/SingularCochainSheaf/ResolutionH1.lean` | C | A | 0.33 |
| `Lib/Topology/Sheaves/SingularCochainSheaf/GlobalUnitH1.lean` | C | A | 0.33 |
| `Lib/Topology/Sheaves/SingularCochainSheaf/GlobalKernelSmall.lean` | C | A | 0.13 |
| `Lib/Topology/Sheaves/PrincipalCoverLocalSystem/CyclicComponentSections.lean` | C | A | 0.34 |
| `Lib/Topology/Sheaves/OpenFiniteClosedFactorization.lean` | C | A | 0.19 |
| `Lib/Topology/Sheaves/FiniteSupport/SkyscraperReconstruction.lean` | C | A | 0.36 |
| `Lib/Topology/Sheaves/FiniteSupport/SkyscraperGlobalSections.lean` | C | A | 0.39 |
| `Lib/Topology/Sheaves/ConstantSheafH1.lean` | C | A | 0.12 |
| `Lib/Topology/Sheaves/ConstantCohomologyPullback.lean` | C | A | 0.45 |
| `Lib/Topology/Homotopy/RelativeDiskLifting.lean` | C | A | 0.20 |
| `Lib/Topology/Homotopy/PuncturedPlaneCyclic.lean` | C | A | 0.39 |
| `Lib/Topology/Homotopy/CellFilling.lean` | C | A | 0.19 |
| `Lib/Topology/Covering/DiagonalQuotient.lean` | C | A | 0.39 |
| `Lib/LinearAlgebra/Dual/Contragredient.lean` | D | B | 0.22 |
| `Lib/GroupTheory/SplitExtension.lean` | D | B | 0.57 |
| `Lib/Data/Int/SignedResidual.lean` | D | B | 0.51 |
| `Lib/CategoryTheory/Sites/Leray/ResolutionTransgression.lean` | C | A | 0.16 |
| `Lib/CategoryTheory/Sites/Leray/ResolutionCohomologyPresheaf.lean` | C | A | 0.26 |
| `Lib/CategoryTheory/Sites/Leray/ResolutionAbutment.lean` | C | A | 0.58 |
| `Lib/CategoryTheory/Sites/Leray/HigherDirectImageSheafification.lean` | C | A | 0.34 |
| `Lib/CategoryTheory/Sites/Leray/FibreStalkEvaluation/CofinalCriterion.lean` | C | A | 0.29 |
| `Lib/CategoryTheory/Sites/Leray/FibreStalkEvaluation.lean` | B | D | 0.17 |
| `Lib/CategoryTheory/Abelian/Injective/CompatibleResolution.lean` | C | A | 0.15 |
| `Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean` | C | A | 0.28 |
| `Lib/AlgebraicTopology/SingularHomology/Chains.lean` | C | A | 0.22 |
| `Lib/AlgebraicTopology/Hurewicz/SphereGenerator.lean` | D | B | 0.21 |
| `Lib/AlgebraicTopology/Hurewicz/DegreeSix.lean` | D | B | 0.57 |
| `Lib/AlgebraicTopology/Hurewicz/CubeSphere.lean` | C | A | 0.29 |
| `Lib/AlgebraicTopology/FundamentalGroup/VanKampen/Character.lean` | C | A | 0.36 |
| `Lib/Algebra/Homology/SpectralSequence/NatLowerEdge.lean` | C | A | 0.38 |
| `Lib/Algebra/Homology/SpectralObject/PostnikovD2.lean` | A | C | 0.14 |
| `Lib/Algebra/Homology/HomologicalComplex/ChainCycleLift.lean` | C | A | 0.47 |
| `Lib/Algebra/Homology/DerivedCategory/Ext/ShortExactAcyclicQuotient.lean` | C | A | 0.40 |
| `Lib/Algebra/Group/ResidualRelations.lean` | D | B | 0.33 |
