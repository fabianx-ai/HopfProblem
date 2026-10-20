# Judgement packet: chokepoint universe pins

Named by the packet receipts as the declarations that force the remaining `.{0}` pins. Lift each (with its file), rebuild the consumers, then re-run the checklist on the files it releases. Envdiff: changed types = the lifted declarations and their dependents, 0 lost.

- `AlgebraicTopology.SingularCochains.complex` / `.chains` (`X : Type`, `AddCommGrpCat.{0}`): packet 01 lifted the cochain interface in `SingularCochains.lean`; check what remains forced in packets 02 and 10 (`PositivePrimitives`, `Vanishing`, `PrimitivesH1`, `SingularChains.SingularSimplex`, `SingularMayerVietoris.SingularHomology (Y : Type)`).
- `TopCat.SheafH1.unitSheaf` (`Cohomology/AcyclicResolutionH1.lean`), `TopCat.ConstantSheaf.sheaf`/`.integralSheaf` (`ConstantPushforward/GlobalSections.lean`, lifted by packet 08? verify), `TopCat.Sheaf.freeOpen`/`freeHomEquiv`, `OpenRestriction.freeOpen`/`cohomologyEquiv` (`OpenRestriction/Cohomology.lean`), `FiniteClosedPushforward.cohomologyEquiv`, `OpenEmbeddingCohomology.openImage`, `ConstantSheafCohomology.pullback`, `pushforwardStalkEquiv`, `integralPushforwardHom_comp_bijective`, `germ_stalkIso_hom_nearbyRestrictionUnit` (`NearbyRestrictionGerm.lean`).
- `Sheaf.cohomologyAddCommGroup` (`Cohomology/AddCommGroup.lean`): the instance is load-bearing (names branch); lifting it to `.{u}` may be possible even though deleting it is not.
- `HasExt.{0}` private instance in `H1Vanishing/Flasque.lean`; `HasExt` pinned to the hom universe in `cochainTransgression`.
- `ULift.{0} ℤ` normalisation target (`CoefficientNormalization.lean`, 13 pins); `ModuleCat.of ℤ ℤ : ModuleCat.{0} ℤ` in `singularChainComplexFunctor`.
- Mathlib's `ModuleCat.hasLimits` at `max v w` (Coproduct, 9 pins): may need `ModuleCat.{max u v}` throughout rather than a lift.
- `TopCat.LocalPredicate` over ℂ (`SquareRoot.lean`, 1 pin).
