# Wave 1 receipt — `Lib/AlgebraicTopology/SingularHomology/MayerVietoris.lean` (mayer)

Base `lib/integration` at `e669bc93`; branch `wave1/mayer`. Judgement: `Lib/reports/round-7/judgement/monoliths.md`,
verdict C (one file for four textbook topics; the definition of singular homology buried in a namespace).

## The cut

Every declaration of the module moves verbatim into one of fourteen modules
`Lib/AlgebraicTopology/SingularHomology/MayerVietoris/<Topic>.lean`; `MayerVietoris.lean` is now a facade
(module docstring + fourteen `public import`s), so all 59 importing files and every name are unchanged.
The definition of singular homology (`SingularMayerVietoris.SingularHomology`, `singularHomologyMap`,
`singularHomologyMap_one`) is in `MayerVietoris/SingularHomology.lean`, three declarations, nothing else.
Import graph of the pieces (from the dump's `uses`, `_proof_n` edges dropped, `deps.py`):
`ChainSequence → SmallChains`; `BiprodSequence, SingularHomology → HomologyLongExact`;
`SmallHomology → ChainSequence, BiprodSequence, SingularHomology`; `FormalSubdivision → FormalChains`;
`Subdivision → AffineSimplex, FormalSubdivision`; `Support → FormalSubdivision`;
`Mesh → AffineSimplex, Support`; `SmallSimplices → SmallChains, Subdivision, Mesh` (+ `ModuleHomology`);
`Sequence → SmallHomology, SmallSimplices`. `SmallChains`, `AffineSimplex`, `SingularHomology` import
`SingularHomology.Chains`; `ChainSequence` imports `Algebra.Homology.MayerVietorisShortExact`;
`HomologyLongExact`, `FormalChains` import only `Mathlib`.

| piece | lines moved (base line range) | declarations | textbook topic |
|---|---|---|---|
| `MayerVietoris/SingularHomology.lean` | 14 (units 927–942) | 3 | the definition of singular homology `H_n(Y; ℤ)` and `singularHomologyMap` (Hatcher §2.1; Mathlib `singularChainComplexFunctor`) |
| `MayerVietoris/HomologyLongExact.lean` | 73 (units 604–687) | 12 | long exact homology sequence of a short exact sequence of chain complexes of ℤ-modules (Mathlib `ShortExact.homology_exact₁/₂/₃`, `δ_apply`; cf. Hatcher §2.1) |
| `MayerVietoris/BiprodSequence.lean` | 219 (units 689–923) | 15 | the same sequence with a biproduct `K ⊞ L` in the middle: `homologyBiprodEquiv`, `biprodSequence_exact_at_*` (Hatcher §2.2) |
| `MayerVietoris/SmallChains.lean` | 259 (units 88–377) | 30 | supported and `(U, V)`-small chains, `smallComplex`, `smallInclusion`, subtype chain inclusion/retraction (Hatcher Prop 2.21, `C_n^𝒰(X)`) |
| `MayerVietoris/ChainSequence.lean` | 197 (units 381–600) | 24 | `0 → C(U ∩ V) → C(U) ⊞ C(V) → C^{U,V}(X) → 0`: `chainSequence`, `chainSequence_shortExact` (Hatcher §2.2, Mayer–Vietoris sequences) |
| `MayerVietoris/SmallHomology.lean` | 152 (units 944–1113) | 19 | homology sequence of the small chain sequence, `smallHomologyComparison`, `rightTransport_*` (Hatcher §2.2) |
| `MayerVietoris/AffineSimplex.lean` | 99 (units 1117–1225) | 11 | affine simplices `[v₀,…,vₙ]` in the standard simplex, `stdVertices`, `simplexBarycenter` (Hatcher, proof of Prop 2.21) |
| `MayerVietoris/FormalChains.lean` | 141 (units 1229–1385) | 17 | formal (linear) chains on a vertex type, cone `b`, boundary, `∂(b c) = c − b(∂c)` (Hatcher, proof of Prop 2.21) |
| `MayerVietoris/FormalSubdivision.lean` | 269 (units 1389–1752) | 20 | barycentric subdivision `S` of formal chains, chain map, homotopy `T` with `∂T + T∂ = 𝟙 − S`, iterates (Hatcher, proof of Prop 2.21, step (2)) |
| `MayerVietoris/Subdivision.lean` | 270 (units 1465–1970) | 22 | `affineChainMap`, subdivision `subdivision X k n` of singular chains and `subdivisionHomotopy` (Hatcher, proof of Prop 2.21, step (3)) |
| `MayerVietoris/Support.lean` | 139 (units 1974–2128) | 17 | supports of formal chains, preservation under boundary/cone/map/subdivision, `*_support_exists` (Hatcher, proof of Prop 2.21, step (1)) |
| `MayerVietoris/Mesh.lean` | 357 (units 2209–2596) | 32 | `vertexBarycenter`, `meshFactor n = n/(n+1)`, mesh estimates, Lebesgue number `exists_lebesgue_number_two` (Hatcher, proof of Prop 2.21, steps (1), (4)) |
| `MayerVietoris/SmallSimplices.lean` | 173 (units 2130–2708) | 12 | realized chains are small, `eventually_subdivision_mem_small`, `smallInclusion_quasiIso`, `smallHomologyEquiv` (Hatcher Prop 2.21) |
| `MayerVietoris/Sequence.lean` | 122 (units 2712–2847) | 15 | `leftHomologyMap`, `rightHomologyMap`, `connectingHomomorphism`, `exact_at_intersection/_pair/_ambient` (Hatcher §2.2) |
| **total** | **2484** | **249** | |

Line counts are the moved units (docstring + declaration); the rest of the base file's 2847 lines is the
header, the module docstring and fourteen `/-! ### -/` section headers (context), see `split_none` below.

Tool use. `split_module.py` was run fourteen times from the base source, once per piece with the stay set
= all other declarations (the tool anchors on the base line ranges, so the pieces cannot be peeled
sequentially from a shrinking file); each run's move file is the piece, the keep file was discarded.
The dump used is `mayer/dump_local.jsonl`, a `--modules`-restricted dump of the same source (the head dump
was not finished when the split ran); its 312 rows have ranges and `typeHash`es identical to the head
dump's (checked row by row). A fifteenth run with an empty stay set (`split_none.json`) confirms that
the context residue is header + docstring + section headers only. Receipts: `mayer/split_<Piece>.json`.
The tool's `--move-imports`/`--move-doc` insertion looks for lines starting with `import `, which this
module-system file (`public import`) has none of; headers (copyright, `module`, imports, module docstring,
`open`, `@[expose] public noncomputable section`, `universe u` where used) were therefore written by hand
and the tool output appended after its copy of the shared prologue (`assemble.py`). The script verifies
that every moved unit's text (sha256 of the receipt) occurs verbatim in the assembled file: 249/249.
Hand edits outside declarations: four `/-! ### -/` headers renamed or added where a non-contiguous piece
made the original header wrong (`FormalSubdivision` l.109 "The subdivision homotopy", `Subdivision`
l.110 "Subdivision of singular chains" added, `SmallSimplices` l.37 "Realized chains and small chains",
the header before `SingularHomology` dropped); `open … Manifold` dropped everywhere (unused);
`universe u` kept only in `HomologyLongExact`, `BiprodSequence` (the only `ModuleCat.{u}` users).

## `Hopf/Proof` moves

None. The module contains no project vocabulary (`grep -n -i 'mo1973\|native\|Hemisphere\|Sphere 2\|dimension\|W4\|receipt'` empty).
Closure over `dump_head.jsonl` (`uses` of every constant of every other `Lib.*` module, closed backwards
inside the module): 246 of the 249 ranged constants are reachable from another `Lib` module (34 `Lib`
modules use constants of the module directly); the three unreachable ones —
`connectingHomomorphism_comp_left`, `formalSubdivisionHomotopy_zero`, `formalSubdivision_zero` — are
textbook consequences (a composite of exact maps is zero; the degree-`0` cases of `T` and `S`) and stay.
`Lib/AxiomAudit.lean` keeps its probe `#print axioms SingularMayerVietoris.exact_at_ambient`.

## Renames, lifts

None (`rename.txt` empty). No universe lifts attempted: every `{X : Type}` statement is left at
universe `0` (listed under Left).

## Docstrings

Computed over the fourteen pieces: 249 non-private declarations, 0 private, 0 without a docstring
(every declaration already carried one at the base; none written). Each piece has a module docstring
stating the mathematics and the textbook result.

## Checks (verbatim)

Lake 5.0.0 (Lean 4.33.0) rejects the jobs flag: `lake build -j3 …` → `error: unknown short option '-j'`
(also `-j 3`, `--jobs=3`, `--threads=3`); all builds below ran without it.

```
$ lake build Lib.AlgebraicTopology.SingularHomology.MayerVietoris.{SmallChains,ChainSequence,HomologyLongExact,BiprodSequence,SingularHomology,SmallHomology,AffineSimplex,FormalChains,FormalSubdivision,Subdivision,Support,Mesh,SmallSimplices,Sequence} Lib.AlgebraicTopology.SingularHomology.MayerVietoris
✔ [8709/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.AffineSimplex (11s)
✔ [8710/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.FormalChains (13s)
✔ [8711/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.HomologyLongExact (13s)
✔ [8712/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChains (15s)
✔ [8713/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SingularHomology (12s)
✔ [8714/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.FormalSubdivision (14s)
✔ [8715/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.BiprodSequence (15s)
✔ [8716/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.ChainSequence (14s)
✔ [8717/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Subdivision (16s)
✔ [8718/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallHomology (15s)
✔ [8719/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Support (19s)
✔ [8720/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Mesh (17s)
✔ [8721/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallSimplices (9.9s)
✔ [8722/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Sequence (8.4s)
✔ [8723/8723] Built Lib.AlgebraicTopology.SingularHomology.MayerVietoris (6.2s)
Build completed successfully (8723 jobs).
done 0
$ lake build Lib
Build completed successfully (9160 jobs).
lib 0
$ lake build Solution S6Shortcuts S6 Challenge
Build completed successfully (9212 jobs).
sol 0
$ lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit
Build completed successfully (9162 jobs).
aud 0
```

Axiom audit (`build2.log`): 3302 `depends on axioms` lines, all ⊆ {propext, Classical.choice, Quot.sound},
`sorryAx` absent; the module's probe: `'SingularMayerVietoris.exact_at_ambient' depends on axioms:
[propext, Classical.choice, Quot.sound]`.

```
$ python3 scripts/lib_stock_census.py --check
ratchet PASS: 123 <= baseline 1648
$ grep -rn '^import Hopf' Lib/ --include=*.lean | wc -l
0
```
(`grep -rn '^import Hopf' Lib/` without the filter hits nine pre-existing lines in `Lib/docs/*.md` and
`Lib/docs/logs/**/*.lean.txt`, unchanged by this work.)

## envdiff

`python3 /home/goblin/lean-agent-ide/tools/envdiff.py dump_head.jsonl dump_after.jsonl --receipt envdiff.json > envdiff.txt`
(`dump_after.jsonl`: `lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib` at the tip, 38260 constants; no rename map).

```
constants before 38248 after 38260 (keys 38146 38158 )
lost 25 added 37 of which source declarations: 0 0 ; names with changed type 24 of which source: 6
  PROOF-NAMING SingularMayerVietoris.inl_rightMap
  PROOF-NAMING SingularMayerVietoris.inr_rightMap
  PROOF-NAMING SingularMayerVietoris.leftMap_fst
  PROOF-NAMING SingularMayerVietoris.leftMap_snd
  PROOF-NAMING SingularMayerVietoris.smallLeftHomologyMap_components
  PROOF-NAMING SingularMayerVietoris.smallRightHomologyMap_components
auxiliary lost/added/changed (not judged): 25 37 18
module moves (source declarations, 1-to-1):
      11  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.AffineSimplex
      15  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.BiprodSequence
      20  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.ChainSequence
      17  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.FormalChains
      20  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.FormalSubdivision
      12  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.HomologyLongExact
      32  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Mesh
      15  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Sequence
       3  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SingularHomology
      30  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallChains
      17  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallHomology
      12  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.SmallSimplices
      22  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Subdivision
      17  Lib.AlgebraicTopology.SingularHomology.MayerVietoris -> Lib.AlgebraicTopology.SingularHomology.MayerVietoris.Support
ambiguous module changes: 0
auxiliary constants that changed module: 47
VERDICT PASS
```

Reconciled: source declarations lost 0, added 0; module moves 243 one-to-one, all
`MayerVietoris -> MayerVietoris.<Piece>` with the planned counts (AffineSimplex 11, BiprodSequence 15,
ChainSequence 20 (+4 below = 24), FormalChains 17, FormalSubdivision 20, HomologyLongExact 12, Mesh 32,
Sequence 15, SingularHomology 3, SmallChains 30, SmallHomology 17 (+2 below = 19), SmallSimplices 12,
Subdivision 22, Support 17); the remaining six of the 249 are the `PROOF-NAMING` names, whose statements
embed an abstracted proof: at the base it was `smallDifferential._proof_1` (the first declaration of the
module that produced that proof term), at the tip the same term is `toSmallLeft._proof_1` (the first
declaration of `ChainSequence` producing it, `smallDifferential` now living in `SmallChains`); Lean names
an abstracted proof after the first declaration of the module that produced it, so the name — and the
type hash — changes when the module boundary moves. Their `uses` without `_proof_n` are equal on both
sides, and they sit in their planned pieces:

| name | planned | module after | typeHash changed | reconciliation |
|---|---|---|---|---|
| `inl_rightMap` | `ChainSequence` | ChainSequence | True | uses equal: True; proof terms ['middleComplex._proof_1', 'smallDifferential._proof_1'] → ['toSmallLeft._proof_1', 'middleComplex._proof_1'] |
| `inr_rightMap` | `ChainSequence` | ChainSequence | True | uses equal: True; proof terms ['middleComplex._proof_1', 'smallDifferential._proof_1'] → ['toSmallLeft._proof_1', 'middleComplex._proof_1'] |
| `leftMap_fst` | `ChainSequence` | ChainSequence | True | uses equal: True; proof terms ['middleComplex._proof_1', 'smallDifferential._proof_1'] → ['toSmallLeft._proof_1', 'middleComplex._proof_1'] |
| `leftMap_snd` | `ChainSequence` | ChainSequence | True | uses equal: True; proof terms ['middleComplex._proof_1', 'smallDifferential._proof_1'] → ['toSmallLeft._proof_1', 'middleComplex._proof_1'] |
| `smallLeftHomologyMap_components` | `SmallHomology` | SmallHomology | True | uses equal: True; proof terms ['middleComplex._proof_1', 'smallDifferential._proof_1'] → ['toSmallLeft._proof_1', 'middleComplex._proof_1'] |
| `smallRightHomologyMap_components` | `SmallHomology` | SmallHomology | True | uses equal: True; proof terms ['middleComplex._proof_1', 'smallDifferential._proof_1'] → ['toSmallLeft._proof_1', 'middleComplex._proof_1'] |

Auxiliary constants (`_proof_n`, equation lemmas, `match_n`): 25 lost / 37 added / 18 changed, 47 changed
module — re-abstracted or realized where first used, not judged. `python3 partition.py`/`deps.py`-style check
over `dump_after.jsonl`: all 249 planned names are in their planned module.

## Left

Each item with the grep that reproduces it at the tip of `wave1/mayer`.

1. **Duplicate development.** `MayerVietoris/{AffineSimplex,FormalChains,FormalSubdivision,Support,Mesh}.lean`
   (formal chains, barycentric subdivision, supports, mesh estimate: 97 declarations) has a twin in
   `Lib/AlgebraicTopology/SingularSmallChains/Barycentric/{AffineSimplex,FormalChains,FormalSubdivision,FormalHomotopy,FormalIteration,FormalSupport,Mesh*,…}.lean`
   with 86 identical short names (`formalCone`, `formalBoundary`, `formalSubdivision`, `formalSubdivisionHomotopy`,
   `meshFactor`, `exists_lebesgue_number_two`, …). The auditors' suggestion (replace the `MayerVietoris` copy by the
   `Barycentric` one) is a deletion, out of scope for this wave. Reproduce:
   `comm -12 <(grep -rhoE '^(theorem|def|abbrev|lemma) [A-Za-z_.]+' Lib/AlgebraicTopology/SingularSmallChains/Barycentric/*.lean | awk '{print $2}' | sed 's/.*\.//' | sort -u) <(grep -hoE '^(theorem|def|abbrev) SingularMayerVietoris\.[A-Za-z_]+' Lib/AlgebraicTopology/SingularHomology/MayerVietoris/{FormalChains,FormalSubdivision,AffineSimplex,Support,Mesh}.lean | awk '{print $2}' | sed 's/.*\.//' | sort -u) | wc -l` → 86.
2. **Duplicate biproduct homology.** `SingularMayerVietoris.homologyBiprodEquiv` (`MayerVietoris/BiprodSequence.lean:112`,
   binary `K ⊞ L`) and `Coproduct.homologyBiproductEquiv` (`Lib/AlgebraicTopology/SingularHomology/Coproduct.lean:385`,
   finite `ι`-indexed) state the same fact; twin named, nothing deleted.
   `grep -n '^def Coproduct.homologyBiproductEquiv\|^def SingularMayerVietoris.homologyBiprodEquiv' Lib/AlgebraicTopology/SingularHomology/Coproduct.lean Lib/AlgebraicTopology/SingularHomology/MayerVietoris/BiprodSequence.lean`.
3. **Namespace of singular homology.** `SingularMayerVietoris.SingularHomology` / `singularHomologyMap` keep the
   theorem-named namespace: 4433 uses in 126 files, so the rename to `SingularHomology.*` the auditors ask for is
   not a small consumer edit. `grep -rl 'SingularMayerVietoris\.\(SingularHomology\|singularHomologyMap\)\b' Lib Hopf Solution.lean S6.lean S6Shortcuts.lean Challenge.lean | wc -l` → 126.
4. **Universe 0.** The space-level statements keep `{X : Type}` (109 binders in `SmallChains`, `ChainSequence`,
   `SmallHomology`, `SingularHomology`, `Subdivision`, `SmallSimplices`, `Sequence`; the affine/formal part is already
   `Type*`, 80 occurrences); no lift attempted, since `SingularChains.singularComplex` and its consumers are pinned at
   `Type` upstream. `grep -c '{X : Type}\|(X : Type)\|{X Y : Type}\|(Y : Type)\|{Y Z : Type}' Lib/AlgebraicTopology/SingularHomology/MayerVietoris/*.lean`.
5. **Exactness as `range = ker`.** `exact_at_intersection/_pair/_ambient` (`MayerVietoris/Sequence.lean:127,135,142`)
   and the `small_exact_at_*`, `biprodSequence_exact_at_*`, `exact_at_*Homology` families state exactness as
   `LinearMap.range f = LinearMap.ker g` rather than as a `ShortComplex.Exact`; a statement change, not this wave.
   `grep -n '^theorem SingularMayerVietoris.exact_at_' Lib/AlgebraicTopology/SingularHomology/MayerVietoris/Sequence.lean`.
6. **`exists_lebesgue_number_two`** (`MayerVietoris/Mesh.lean`) is the two-set case of Mathlib's
   `lebesgue_number_lemma_of_metric`, which its proof already uses (`grep -n lebesgue_number_lemma_of_metric Lib/AlgebraicTopology/SingularHomology/MayerVietoris/Mesh.lean` → l.130); twin named, kept.
7. **Facade.** `MayerVietoris.lean` stays as a facade; consumers (59 `import` lines) unchanged, `Lib.lean` unchanged.
8. **Jobs flag.** `lake build -j3` is not accepted by Lake 5.0.0 (`error: unknown short option '-j'`); builds ran with
   Lake's default parallelism.
