# Wave 2: `Lib/Geometry/Manifold/Transversality/Basic.lean`

Agent: Claude Opus 5.5 (`claude-opus-5-5`). Started 2026-10-01 18:42 CEST, ended 2026-10-01 ~20:00 CEST.
Branch `wave2/transversality`, base `3760f829`; commits `f975171c` (split), `a3d7b5ad` (import
trims), then this receipt. The agent before this one was stopped while still reading and made no commits.

Source: 3,220 lines, 136 declarations (verdict C in `Lib/reports/round-7/judgement/monoliths.md`).

## The cut

`split_module.py` was run once per piece on a copy of the original source (stay = all − piece), so
every piece came straight out of the original text. The receipts are
`transversality/split_<Piece>.json` and the partition is `transversality/pieces.py`. The tool never
refused, and no declaration was split by hand. Lines are those of the original file, docstrings
included.

| piece `Lib/Geometry/Manifold/Transversality/…` | lines moved | decls | textbook topic |
|---|---|---|---|
| `Diffeomorph` | 65–121 | 2 | diffeomorphisms whose underlying maps unfold definitionally (variants of Mathlib's `Diffeomorph.toPartialDiffeomorph`, `IsLocalDiffeomorph.diffeomorphOfBijective`) |
| `RegularValues` | 123–322 | 5 | surjective derivative is chart-independent and open; Sard's theorem in equal dimension (G–P §1.7) |
| `Transverse` | 324–379, 464–749, 3207–3220 | 11 | the relation `f ⋔ g` at `(x, y)`: chart criterion, openness in families, invariance (G–P §2.3) |
| `Parametric` | 381–462 | 2 | transversality after a generic translation (G–P §2.3, Hirsch Ch. 3) |
| `MorseBelt` | 751–1172 | 28 | belt-sphere neighbourhood coordinates of a Morse chart (cf. Milnor, h-cobordism §3) |
| `CenteredChart` | 1174–1219 | 5 | translations, charts centred at a point |
| `SupportedIsotopy` | 1221–1548, 2908–2956, 3017–3041 | 13 | compactly supported isotopies, isotopy extension through a chart, shears (cf. Hirsch Ch. 8 §1) |
| `LinearFramePaths` | 1655–1727, 2242–2385 | 13 | `SL(n,ℝ)` path connected, two path components of `GL(n,ℝ)` |
| `GermLinearization` | 1837–2206 | 8 | linearising a germ by a compactly supported isotopy |
| `GermRealization` | 1550–1653, 1729–1835, 2208–2240, 2387–2551 | 13 | germs realised by supported diffeomorphisms; aligning two charts with the same centre |
| `DiskShrinking` | 2553–2827 | 29 | radial diffeomorphisms `x ↦ φ(‖x‖²)•x`, the disc-shrinking isotopy |
| `DiscTheorem` | 2829–2906, 2958–3015, 3043–3130 | 5 | the disc theorem (Hirsch Thm 8.3.1; Palais) |
| `Homogeneity` | 3132–3205 | 2 | homogeneity lemma (cf. Milnor, *Topology from the Differentiable Viewpoint* §4) |

Total: 136 declarations. `Basic.lean` is now a facade: a rewritten module docstring listing the
pieces and their 13 `public import`s, nothing else. No consumer and not `Lib.lean` was edited. No
piece name collides with an existing file; the directory held only `Basic.lean`.

`split_module.py` was run without `--move-imports`, so the known bug did not arise. The piece
headers (imports and module docstring) were written by a script. Each piece first kept the original
eight imports plus the pieces it uses. Commit `a3d7b5ad` then trimmed them: every piece keeps
`Mathlib` and the smallest subset of the six original project imports whose import closure contains
the modules of the constants it uses (computed from the dump, confirmed by the builds below). The
duplicate `Mathlib.Geometry.Manifold.LocalDiffeomorph` was dropped. The original file had no
`set_option maxSynthPendingDepth`, no kitchen-sink `open scoped` and no `universe` line any more, so
there was nothing to drop. Each piece keeps `open Set Function Filter Manifold Topology` and
`open scoped ContDiff Matrix NNReal`.

## `Hopf/Proof` moves: none

The closure argument, a script over `dump_head.jsonl`: we take the constants of the module that are
reachable backwards, through `uses`, from any constant of another `Lib` module. All 136 ranged
declarations are in that set. The file has no dimension-6, `Sphere 2` or `mo1973` material, so
nothing moves.

## Renames: none

There are no `mo1973` names. `rename.txt` holds a single comment line. The `Native*` names are
listed under "Left".

## Lifts: none

All binders were already `Type*`.

## Docstrings

Counted, not estimated: for each of the 136 ranged constants, the source line at the start of its
dump range begins with `/--`. That gives 136 of 136; none was missing and none was rewritten. The
13 new module docstrings are new, and so is the facade's.

## Checks (at `a3d7b5ad`; the receipt commit touches only `Lib/reports/`)

- `lake build` of the facade and the 13 pieces: `Build completed successfully (8767 jobs).`
- `lake build Lib`: `Build completed successfully (9291 jobs).`
- `lake build Solution S6Shortcuts S6 Challenge`: `Build completed successfully (9350 jobs).`
- `lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit`: `Build completed successfully (9293 jobs).`
  The union of the reported axiom sets over all 3,302 `depends on axioms` lines is
  `{propext, Classical.choice, Quot.sound}`, and there is no `sorryAx`.
- `python3 scripts/lib_stock_census.py --check`: `stock declarations under Hopf/: 123 …` and
  `ratchet PASS: 123 <= baseline 1648`.
- `grep -rn '^import Hopf' Lib/` gives 9 hits. All of them are in `Lib/docs/**/*.md|*.txt`, which
  this branch does not touch (`git diff --stat 3760f829 -- Lib/docs` is empty). With
  `--include=*.lean` it gives 0 hits.
- dump + envdiff (`transversality/envdiff.txt`): `constants before 38301 after 38301`, `lost 0
  added 0`, `names with changed type 0`, the 13 module moves equal to the table above (also checked
  name by name against `pieces.py`: 0 mismatches), 64 auxiliary constants changed module along with
  their owners, `VERDICT PASS`.

## Left

1. **`Native*` vocabulary.** These names are kept because the consumer edit is large:
   `NativeTransversality.At` alone has 82 references in 23 `.lean` files. The suggested names are
   `NativeTransversality.At` → `IsTransverseAt`, `NativeSubmersion.*`,
   `TransverseCoordinates.*native_translations`, `NativeParametrization.*`,
   `TransverseGerms.native_transversality_partial_diffeomorph_iff`,
   `SupportedGerms.exists_native_disk_germ_alignment`.
   Reproduce: `grep -nE "^(theorem|def) \S*[Nn]ative" Lib/Geometry/Manifold/Transversality/*.lean`
   (15 lines) and `grep -rn "NativeTransversality.At" Lib Hopf --include=*.lean | wc -l` (82).
2. **`MorseBelt` belongs in `Lib/Geometry/Manifold/Morse/`.** This is the judgement's suggestion. It
   stayed under `Transversality/` as the assignment directs, and it is the only piece that still
   needs `Morse.SurgeryWindows`. Reproduce: `grep -n "^public import" Lib/Geometry/Manifold/Transversality/MorseBelt.lean`.
3. **Heavy imports for a few constants.** Several pieces import `Morse.Existence` or
   `Morse.CubicFlow` only for a few general lemmas, e.g. `PartialChart.bijective_mfderiv` and
   `MorsePerturbation.contDiffOn_spatialDerivative`. Importing their home modules directly would be
   finer, but those modules are not in the original list. Reproduce: `grep -n "^public import Lib" Lib/Geometry/Manifold/Transversality/*.lean`.
4. **Mathlib duplicates by design.** `Diffeomorph.toPartialDiffeomorph'` and
   `IsLocalDiffeomorph.diffeomorph'` are transparent twins of Mathlib's
   `Diffeomorph.toPartialDiffeomorph` and `IsLocalDiffeomorph.diffeomorphOfBijective`. Reproduce:
   `grep -n "Transparent variant" Lib/Geometry/Manifold/Transversality/Diffeomorph.lean`.
5. **Mathlib gap.** Mathlib has no path-connectedness of `SL(n, ℝ)`, so `LinearFramePaths` is
   genuine. Reproduce: `grep -rln SpecialLinearGroup .lake/packages/mathlib/Mathlib | xargs grep -ln "Joined\|PathConnected"`
   prints nothing.
6. **Declaration in the root namespace.** `exists_small_supported_germ` sits in the root namespace.
   Reproduce: `grep -n "^theorem exists_small_supported_germ" Lib/Geometry/Manifold/Transversality/SupportedIsotopy.lean`.
