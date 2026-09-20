# Judgement packet: D files, part c

For each file: the auditors name the general declarations worth keeping; keep those in Lib (renamed to standard names), move the rest back under Hopf/Proof/<path>.lean with its consumers rerouted; envdiff shows moves only.

## Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean  (1 declarations, 35 lines)
verdict: D (special case Mathlib already has: `Ext.instAddCommGroup`)
twin: Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean (`Sheaf.H F n` is `Ext` and inherits `AddCommGroup` via `CategoryTheory.Abelian.Ext.instAddCommGroup`)
findings:
- l.29 `instance cohomologyAddCommGroup ... : AddCommGroup (Sheaf.H.{0} F n) := Ext.instAddCommGroup`: the proof term is the Mathlib instance itself; the declaration exists only because `Sheaf.H` is an `abbrev`-unfolding issue at universe 0 — a workaround, not a theorem
- l.15–17 docstring: "This module owns that unconditional instance ... so generic sheaf-cohomology developments share one discoverable declaration" — ownership language
- restricted to `TopCat.{0}` / `AddCommGrpCat.{0}`
suggestion: delete the file and use `inferInstance`/`Ext.instAddCommGroup` at the use sites (or fix the instance-resolution gap upstream if `Sheaf.H` genuinely fails to find it)

## Lib/Topology/Sheaves/Cohomology/SphereTwo.lean  (4 declarations, 149 lines)
verdict: D (proof-specific: a special case of the project's own `CoveringDimension.lean`, wrapped for the application)
twin: Godement II.5.12 (covering-dimension vanishing) — the general theorem is already in `Lib/Topology/Sheaves/Cohomology/CoveringDimension.lean`; no Mathlib twin
findings:
- l.12–25 module docstring cites "Corollary 6.5, equation (9)", "equation (14)", "equation (10)" — the project's manuscript; l.55–75 docstring discusses "the application's pair of degree-three and degree-four vanishings", "a possibly nonconstant higher direct-image sheaf", "constructibility" — application commentary, not mathematics of the statement
- l.40 `derivedGlobalSections_isZero_of_homeomorph_sphereTwo`, l.80 the projective-dimension reformulation: both are `CoveringDimension.derivedGlobalSections_isZero_of_coveringDimensionLE` at `n = 2` plus `Lib/Topology/Dimension/SphereTwo`; a textbook would state "for a compact metrisable space of dimension ≤ n" and never single out S²
- `SphereTwo` in the file name and `TopCat.{0}` fixed; l.28–30 repeated `local instance`s
- l.8 imports `Lib.CategoryTheory.Sites.Leray.ResolutionTransgression` — unrelated to the statement
suggestion: move the file to `Hopf/Proof` (or `W4W1`) next to its consumer; if a library form is wanted, state it for compact metrisable spaces of covering dimension ≤ n

## Lib/Topology/Sheaves/SheafificationLocal.lean  (7 declarations, 89 lines)
verdict: D (main statements are Mathlib's `Presheaf.isLocallySurjective_toSheafify` and `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`, unpacked)
twin: Mathlib/CategoryTheory/Sites/LocallySurjective.lean (`isLocallySurjective_toSheafify`), Mathlib/Topology/Sheaves/LocallySurjective.lean (`TopCat.Presheaf.isLocallySurjective_iff`), Mathlib/Topology/Sheaves/Stalks.lean (`stalkFunctor_map_unit_toSheafify_isIso`, used verbatim at l.46)
findings:
- l.11–15 module docstring: two sentences, no `## Main results`
- l.37 `sheaf P` and l.41 `unit P` are aliases for `(presheafToSheaf _ _).obj P` and `toSheafify _ P` with no docstrings; every downstream file must then unfold them
- l.53 `exists_local_representative` is `isLocallySurjective_toSheafify` read through `TopCat.Presheaf.isLocallySurjective_iff`; l.66 `germ_unit_eq_iff` and l.77 `exists_restriction_eq_of_germ_unit_eq` follow from the stalk iso plus `TopCat.Presheaf.germ_eq`
- 3 missing docstrings (l.37, 41, 48); `TopCat.{0}` / `AddCommGrpCat.{0}` only
suggestion: delete `sheaf`/`unit`, keep `exists_local_representative` as a one-line `TopCat.Presheaf` lemma in terms of `toSheafify`, and derive the two germ lemmas from `germ_eq`
