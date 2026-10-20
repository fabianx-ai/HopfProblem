# Wave 2 receipt — `riemann`: `Lib/Analysis/Complex/RiemannMapping.lean`

Base `lib/integration` at `3760f829`; branch `wave2/riemann`; commits `e1cfd7a8..` (listed at the end).
Agent: Claude Opus 5.5, model ID `claude-opus-5-5`; start 2026-10-01 15:38:41 CEST, end 2026-10-01 16:13:16 CEST (receipt commit).
(A previous agent had only read the file; nothing of its work was committed.)
Verdict of `Lib/reports/round-7/judgement/monoliths.md`: C (three topics merged, triangle-specific roots,
lane narrative in the docstring). Twins: Ahlfors, *Complex Analysis*, Ch. 6 §1 / Rudin, *Real and
Complex Analysis*, Thm 14.8 (Riemann mapping theorem); Carathéodory/Schwarz boundary extension
(Ahlfors Ch. 6 §1.4, Pommerenke, *Boundary Behaviour of Conformal Maps*, §2–3).

## The cut

All 181 ranged declarations of the base file were moved by `split_module.py`, one run per piece against
the base file (stay set = all constants except the piece's; receipts `riemann/split_<Piece>.json`).
`RiemannMapping.lean` is now a facade importing the nine `Lib` pieces (nothing else). Line numbers are
those of the base file; "unit lines" count the moved units (docstrings and attributes included).

| piece | lines moved | declarations | textbook topic |
|---|---|---|---|
| `Lib/…/RiemannMapping/Existence` | 441–788 (325 unit lines, 22 units) | `RiemannMapping.uniformEquicontinuousOn_of_thickening_subset_of_forall_norm_le` … `riemannMap_spec` | the Riemann mapping theorem by normal families and Koebe maximization (Ahlfors Ch. 6 §1.1; Rudin Thm 14.8) |
| `Lib/…/RiemannMapping/DiscBoundaryEscape` | 211–296, 1288–1321 (113 unit lines, 7 units) | `RiemannMapping.isCompact_discHomeomorph_preimage_closedBall` … `RiemannBoundary.tendsto_norm_discHomeomorph_in_boundary_chart` | a homeomorphism onto the disc is proper: `‖e z‖ → 1` at the boundary (Pommerenke §2.1) |
| `Lib/…/RiemannMapping/HalfStripChart` | 298–437, 2092–2144, 2361–2400 (205 unit lines, 31 units) | `RiemannBoundary.logHalfStrip` … `halfStripExp_im_pos` | the chart `a - i c log q` of a half-strip end, its inverse, its one-point compactification (cf. Ahlfors Ch. 6 §2) |
| `Lib/…/RiemannMapping/RectanglePrimitive` | 792–953 (150 unit lines, 13 units) | `RiemannBoundary.openRectangle` … `exists_continuous_primitive_openRectangle_of_norm_le` | holomorphic functions on an open rectangle have (Lipschitz-extendable) primitives (Ahlfors Ch. 4 §1.3–1.4) |
| `Lib/…/RiemannMapping/ModulusOneReflection` | 955–1286 (321 unit lines, 12 units) | `RiemannBoundary.hasDerivAt_horizontal` … `exists_analytic_extension_of_modulus_one` | gluing across a segment with vanishing jump; Schwarz reflection in the circle (Ahlfors Ch. 4 §6.5; Rudin Thm 11.14) |
| `Lib/…/RiemannMapping/BoundaryDerivative` | 1325–1533 (194 unit lines, 16 units) | `RiemannMapping.im_mul_exp_real` … `deriv_ne_zero_of_upper_halfPlane_to_unitDisc` | a map of the half-plane into itself (or into the disc) analytic at a boundary point has nonzero derivative there |
| `Lib/…/RiemannMapping/ConformalExtension` | 1535–1547, 1926–2021, 2146–2209 (171 unit lines, 5 units) | `RiemannMapping.exists_boundary_chart_target_ball`, `RiemannBoundary.norm_lt_one_iff_im_pos_eventually` … `exists_conformal_extension_discHomeomorph_at_ideal_vertex` | conformal extension of a disc map across free analytic arcs and at strip ends (Ahlfors Ch. 6 §1.4; Pommerenke §3.3) |
| `Lib/…/RiemannMapping/PrincipalRoot` | 1551–1694 (128 unit lines, 17 units) | `RiemannBoundary.principalRoot` … `principalRoot_pow_of_sector` | the principal `n`-th root, corner straightening for a corner of opening `π / n` (Ahlfors Ch. 6 §2.2) |
| `Lib/…/RiemannMapping/DiscCompactification` | 2023–2090, 2213–2338 (181 unit lines, 15 units) | `RiemannBoundary.discHomeomorphInverse` … `closedDiscHomeomorph_coe` | topological Carathéodory extension to the closure (Pommerenke Thm 2.6) |
| `Hopf/Proof/…/RiemannMapping/TriangleNormalization` | 68–209, 2342–2357 (141 unit lines, 17 units) | `TriangleRiemannNormalization.*` (14), `RiemannMapping.triangleSideParameter*` (3) | project: cross-ratio normalization of a disc triangle |
| `Hopf/Proof/…/RiemannMapping/SectorRoots` | 1696–1922 (200 unit lines, 26 units) | `RiemannBoundary.cubic_sector_slack` … `analyticOnNhd_rotatedPrincipalRootFour_upper` | project: the roots for the corner exponents 3 and 4 |

Refinement of the auditors' suggestion (`RiemannMapping.lean` = l.453–800, `RiemannBoundary.*` to a
Carathéodory/SchwarzReflection file): the boundary material is cut into seven topic pieces under
`RiemannMapping/` instead of being appended to `SchwarzReflection.lean` (that would edit a second
module and make it import the rectangle primitives; see "Left"). The core is `Existence`, not the facade,
because the facade must contain imports only. `Steps.lean` (already a piece at the base) is unchanged
and imported by `Existence`.

Context handling: the tool writes the context (copyright, imports, module docstring, `open`,
`noncomputable section`, the `/-! ### -/` headers) to every output; in each piece the header was
replaced by the piece's imports and a new module docstring (`riemann/../header.py` in the scratch), all
`/-! ### -/` headers were dropped (each piece is one section). Imports: `Mathlib` plus the `Lib`
modules used directly (from the dump's `uses`): `Existence` ← `RiemannMapping.Steps`;
`ModulusOneReflection` ← `SchwarzReflection`, `RectanglePrimitive`; `HalfStripChart` ←
`DiscBoundaryEscape`; `ConformalExtension` ← `DiscBoundaryEscape`, `HalfStripChart`,
`ModulusOneReflection`, `BoundaryDerivative`; `TriangleNormalization` ← `Mobius` (which imports
`RiemannSphere`); `SectorRoots` ← `PrincipalRoot`. The facade's transitive closure still contains every
module of the base import list (`Steps`, `SchwarzReflection`, `Mobius`, `RiemannSphere`), so the
consumers `Cousin`, `SquareRoot` need no change. `import Mathlib` was not narrowed.

Verbatimness (at the split commit `e1cfd7a8`): a script recomputed every moved unit's text from the base
file and found it in its piece: 181 units checked, 0 missing, 181 of 181 names, no duplicates, none left
behind. The docstring commit then rewrote 85 docstrings on purpose (below); `envdiff` confirms the
environment.

## `Hopf/Proof` moves (commit `8e8fe025`)

Moved: `TriangleNormalization` (`TriangleRiemannNormalization.discCoordinate`, `_injective`, `_ne`,
`_norm_le`, `punctureMap`, `_isEmbedding`, `_surjective`, `punctureHomeomorph`,
`normalizationHomeomorph`, `_apply`, `_first`, `_second`, `_strict_iff`,
`normalization_orientation_ne_zero`; `RiemannMapping.triangleSideParameter`, `_zero`,
`continuousAt_triangleSideParameter_zero`) and `SectorRoots` (`cubic_sector_slack`,
`quartic_sector_slack`, `principalRoot_three_upper`, `_ofReal_nonneg_im`, `_ofReal_nonpos_boundary`,
`_real_boundary`, `quarticRootRotation` with `_re`, `_im`, `norm_`, `_ne_zero`, `_pow_four`,
`rotatedPrincipalRootFour` with `_pow`, `_zero`, `norm_`, `_re`, `_im`, `_re_add_im`, `_upper`,
`_ofReal_nonneg_boundary`, `_ofReal_nonpos_im`, `_real_boundary`, `continuousOn_…_closedUpper`,
`continuousAt_…_zero`, `analyticOnNhd_…_upper`). Reason: the judgement names these as the project's
triangle normalization and exponent-specific roots with no textbook counterpart. The general
`principalRoot` (any `n`) stays in `Lib`.

Closure argument: a script over `dump_head.jsonl` (`closure.py` in the scratch) walks the reverse
`uses` graph from every constant of the module; no constant of `Lib.Analysis.Complex.RiemannMapping`
is reachable from a constant of another `Lib` module (the set that must stay is empty; `Cousin` and
`SquareRoot` import the module but use none of its constants). The only user of any constant of the
module outside it is `Hopf.Proof.LCP.AnalyticFillings`, which now has
`import Hopf.Proof.Analysis.Complex.RiemannMapping.TriangleNormalization` and `…SectorRoots`
immediately after its `import Lib.Analysis.Complex.RiemannMapping`. `lake build Lib` is green after the
move; `grep -rn '^import Hopf' Lib/ --include=*.lean` is empty. `Lib/AxiomAudit.lean` probes only
`RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero` (stays); nothing moved to
`Hopf/Proof/AxiomAudit.lean`.

Kept in `Lib` although the judgement lists them as project normalisation: `logHalfStrip*`,
`onePointLogHalfStrip*`, `onePointDomain*`, `halfStripExp*` and the ideal-vertex extension. Their
statements quantify over an arbitrary domain `D`, base `a` and width `c > 0`; no triangle occurs in
them, and they are the standard chart at an infinite vertex.

## Renames

None (`riemann/rename.txt` is empty but for a comment). No `mo1973` names in the file; the namespaces
`RiemannMapping`/`RiemannBoundary` on general lemmas are listed in "Left".

## Universe lifts

None: no declaration of the file binds `Type` or uses `.{0}` (`grep -n ': Type}\|\.{0}'` on the pieces
is empty); every binder was already `Type*` or `Set ℂ`.

## Docstrings (commit `4398ed1c`)

Computed over the nine `Lib` pieces: 138 declarations, 0 `private`, 138 with a docstring, 0 missing
(`grep -c '^/--'` summed = 138 = the declaration count of the pieces in the dump). None was missing at
the base; 85 were rewritten because they were vague or wrong, each written from the declaration's
binders and conclusion (examples: `FunctionSpace` was "holomorphic maps to the disc" but is all
functions `ℂ → ℂ` with uniform convergence on compact subsets of `U`; `riemannMap_spec` was "the
maximizing normalized map"; `exists_unit_upperHalf_power_direction` said "upper half-plane" for a
lower-half-plane conclusion; the "THE HEADLINE" and "Rudin 14.8-adjacent" phrasings). Every piece and
both `Hopf/Proof` modules have a module docstring stating the mathematics; the facade's docstring lists
the pieces; the lane narrative ("lane-A MayerVietoris-style merge, recorded in Lib/reports/A.md") is gone.

Preamble (commit `d34f65a4`): `open Set Function Filter Manifold Topology` → `open Set Function
Filter Topology` in every piece; `open scoped ComplexConjugate ContDiff Interval NNReal
UniformConvergence Uniformity` reduced per piece to the scopes whose notation it uses (`Existence`:
`ContDiff UniformConvergence Uniformity`; `RectanglePrimitive`: `Interval NNReal`;
`ModulusOneReflection`, `ConformalExtension`: `ComplexConjugate`; others: none). The base file had no
`set_option maxSynthPendingDepth`, `universe` or `Modular`/`UpperHalfPlane` scope (the judgement's
finding referred to an older revision).

## Build lines

All under `nohup`, from the worktree root, Lake 5.0.0 (Lean 4.33.0), `taskset -c 9,10,11`, no `-j`.
Result lines, verbatim:

```
lake build Lib.Analysis.Complex.RiemannMapping                         Build completed successfully (8721 jobs).   (commit e1cfd7a8)
lake build Lib.Analysis.Complex.RiemannMapping Hopf.Proof.Analysis.Complex.RiemannMapping.TriangleNormalization
  Hopf.Proof.Analysis.Complex.RiemannMapping.SectorRoots Hopf.Proof.LCP.AnalyticFillings
                                                                        Build completed successfully (8993 jobs).   (commit 8e8fe025)
lake build Lib.Analysis.Complex.RiemannMapping                         Build completed successfully (8719 jobs).   (commit 4398ed1c)
lake build Lib.Analysis.Complex.RiemannMapping Hopf.Proof.Analysis.Complex.RiemannMapping.TriangleNormalization
  Hopf.Proof.Analysis.Complex.RiemannMapping.SectorRoots              Build completed successfully (8721 jobs).   (commit d34f65a4)
lake build Lib                                                          Build completed successfully (9287 jobs).   (commit d34f65a4)
lake build Solution S6Shortcuts S6 Challenge Lib.AxiomAudit Hopf.Proof.AxiomAudit
                                                                        Build completed successfully (9350 jobs).   (commit d34f65a4)
```

Axiom audit (the last log): 3303 `depends on axioms` lines, distinct axioms `Classical.choice`,
`Quot.sound`, `propext`; `sorryAx` occurrences 0.
`python3 scripts/lib_stock_census.py --check`: `ratchet PASS: 123 <= baseline 1648`.
`grep -rn '^import Hopf' Lib/ --include=*.lean`: empty.

## envdiff

`lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib` at `d34f65a4` (38301 constants, rename map
0 entries), then `envdiff.py dump_head.jsonl dump_after.jsonl --receipt riemann/envdiff.json >
riemann/envdiff.txt`:

```
constants before 38301 after 38301 (keys 38199 38199 )
lost 0 added 0 of which source declarations: 0 0 ; names with changed type 0 of which source: 0
auxiliary lost/added/changed (not judged): 0 0 0
module moves (source declarations, 1-to-1):
      26  Lib.Analysis.Complex.RiemannMapping -> Hopf.Proof.Analysis.Complex.RiemannMapping.SectorRoots
      17  Lib.Analysis.Complex.RiemannMapping -> Hopf.Proof.Analysis.Complex.RiemannMapping.TriangleNormalization
      16  Lib.Analysis.Complex.RiemannMapping -> Lib.Analysis.Complex.RiemannMapping.BoundaryDerivative
       5  Lib.Analysis.Complex.RiemannMapping -> Lib.Analysis.Complex.RiemannMapping.ConformalExtension
       7  Lib.Analysis.Complex.RiemannMapping -> Lib.Analysis.Complex.RiemannMapping.DiscBoundaryEscape
      15  Lib.Analysis.Complex.RiemannMapping -> Lib.Analysis.Complex.RiemannMapping.DiscCompactification
      22  Lib.Analysis.Complex.RiemannMapping -> Lib.Analysis.Complex.RiemannMapping.Existence
      31  Lib.Analysis.Complex.RiemannMapping -> Lib.Analysis.Complex.RiemannMapping.HalfStripChart
      12  Lib.Analysis.Complex.RiemannMapping -> Lib.Analysis.Complex.RiemannMapping.ModulusOneReflection
      17  Lib.Analysis.Complex.RiemannMapping -> Lib.Analysis.Complex.RiemannMapping.PrincipalRoot
      13  Lib.Analysis.Complex.RiemannMapping -> Lib.Analysis.Complex.RiemannMapping.RectanglePrimitive
ambiguous module changes: 0
auxiliary constants that changed module: 58
VERDICT PASS
```

Moves only: 181 source declarations, each count equal to the piece's row in the table; 58 auxiliaries
(`eq_n`, `_proof_n`) moved with their parents.

## Left

- `ModulusOneReflection` (reflection across a modulus-one arc) belongs next to
  `Lib/Analysis/Complex/SchwarzReflection.lean` (judgement); kept as its own piece so that this wave edits
  no second module. `grep -n '^theorem' Lib/Analysis/Complex/RiemannMapping/ModulusOneReflection.lean`
- `RectanglePrimitive` is not a duplicate of Mathlib, contrary to the judgement: Mathlib v4.33.0
  `Analysis/Complex/HasPrimitives.lean` proves exactness only on balls and on `univ`
  (`IsConservativeOn.isExactOn_ball`, `DifferentiableOn.isExactOn_ball`, `isExactOn_univ`); the
  rectangle (or convex-set) version is a candidate for upstreaming.
  `grep -n 'isExactOn' .lake/packages/mathlib/Mathlib/Analysis/Complex/HasPrimitives.lean`
- Namespaces: general lemmas carry `RiemannMapping.`/`RiemannBoundary.` prefixes where Mathlib would use
  `Complex.` (`RiemannMapping.im_mul_exp_real`, `RiemannBoundary.norm_sub_inv_conj`,
  `RiemannBoundary.principalRoot`, `RiemannBoundary.openRectangle`, …) or `OpenPartialHomeomorph.`
  (`RiemannMapping.exists_boundary_chart_target_ball`); not renamed (consumer
  `Hopf/Proof/LCP/AnalyticFillings.lean` uses 42 of the `Lib` declarations; no Mathlib-style name was certain for all).
  `grep -c 'RiemannBoundary\.\|RiemannMapping\.' Hopf/Proof/LCP/AnalyticFillings.lean`
- The judgement's "general corner exponent `z ↦ z^{π/α}`" is only done for `α = π / n`
  (`PrincipalRoot`); the exponent-3/4 statements were moved to `Hopf/Proof`, not generalized.
  `grep -n 'principalRoot 3\|principalRoot 4' Hopf/Proof/Analysis/Complex/RiemannMapping/SectorRoots.lean`
- `RiemannMapping.unitDisc` (an `Opens ℂ`) duplicates `Metric.ball 0 1`/Mathlib's `Complex.UnitDisc` in
  role; kept (used by `riemannMap_spec` and the consumer).
  `grep -n 'def RiemannMapping.unitDisc' Lib/Analysis/Complex/RiemannMapping/Existence.lean`
- `import Mathlib` in every piece not narrowed to the Mathlib modules used.
  `grep -n '^import Mathlib$' Lib/Analysis/Complex/RiemannMapping/*.lean`

## Commits

`e1cfd7a8` split (tool, facade) · `8e8fe025` move to `Hopf/Proof` · `4398ed1c` docstrings ·
`d34f65a4` `open` trims · the commit adding this receipt and `riemann/` (split receipts,
`envdiff.json`, `envdiff.txt`, `rename.txt`).
