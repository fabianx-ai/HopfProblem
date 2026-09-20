# Round 7 checklist packet 05

Base: the merged head after the preamble and names branches (see the task prompt). Rubric: `Lib/reports/textbook-audit/RUBRIC.md`; per-file findings: `grep -A14 '^## <path>' Lib/reports/textbook-audit/group-*.log`.

| file | audit | work | twin (from the audit) | suggestion (from the audit) |
|---|---|---|---|---|
| `Lib/Geometry/Manifold/Transversality/Basic.lean` (2904 l.) | C | docstrings 2/135 | Hirsch, Differential Topology Ch. 2–3 and Guillemin–Pollack Ch. 2 (named in docstring); Palais's disc theorem for `DiskS | move the `MorseHandle`/`SignedMorseChart`/`MorseSurgeryData` block (l.703–1060) to `Morse/`, rename `NativeTransversality.At` → `IsTransverseAt` (and drop "nati |
| `Lib/Geometry/Manifold/Whitney/AnnularExtension.lean` (795 l.) | C | docstrings 0/60 | Milnor, Lectures on the h-cobordism theorem §§5–6 (named in docstring); the sphere-map results `sphereMap_nullhomotopic_ | split out `SphereCone`+`AnnularExtension` (→ Topology) and the three sphere-nullhomotopy theorems (→ AlgebraicTopology, documented, replacing `Sphere n` by Math |
| `Lib/Geometry/Manifold/Whitney/BigonModel.lean` (482 l.) | C | docstrings 0/52 | Milnor, Lectures on the h-cobordism theorem §6, Thm 6.6 (the Whitney lemma; named in docstring); Mathlib: none (genuine  | parametrise `Space` by the two normal factors (`Space F₁ F₂ := (ℝ × ℝ) × (F₁ × F₂)`, sheets `ℝ × F₁`, `ℝ × F₂`) so the model is Milnor's, and add one-line docst |
| `Lib/Geometry/Manifold/Whitney/CleanStrips.lean` (2533 l.) | C | docstrings 0/140 | Milnor, Lectures on the h-cobordism theorem §§5–6 (named in docstring); `finite_transverse_intersections` (l.567) and `i | extract `exists_clean_crossingChart` + `finite_transverse_intersections` into a documented `Transversality/Crossing.lean`, move the `MorseSurgeryData.beltInters |
