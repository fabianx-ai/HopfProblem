# Wave 1 receipt — `cross` (`Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean`)

Base `lib/integration` at `e669bc93`; branch `wave1/cross`; commits `44609e2b … the receipt commit`.
Judgement entry: verdict C (left degree fixed to 1 and 2; half the file in the project namespace;
`_mo1973_*` names). Twin: Hatcher, *Algebraic Topology*, §3.B.

## Commits

`44609e2b` whitespace normalisation · `725e956b` split + facade · `0c66b4a6` rename ·
`fee80998` import trims · `f6b68450` one consumer qualification · receipt commit (this file,
`Lib/reports/wave-1/cross/`: `rename.txt`, `envdiff.json`, `envdiff.txt`, `split-<Piece>.receipt.json`,
`closure.json`, `linemap.json`, `plan.json`).

## The cut

Nine pieces under `Lib/AlgebraicTopology/SingularHomology/CrossProduct/`; the original module is a
facade (`public import` of the nine pieces + module docstring, nothing else). Consumers unchanged
except for the rename below; `Lib.lean` not edited.

| piece | source lines moved | declarations | textbook topic |
|---|---|---|---|
| `Multilinear` | 416 | 30 | ℤ-bilinear/trilinear currying and composition, lifts of simplex-wise maps to singular and formal chains, the two `Module ℤ` instances (Hatcher §3.B, "extend bilinearly from generators") |
| `Formal` | 558 | 26 | formal point/edge/triangle cross products = triangulations of `Δᵖ × Δ^q`, `p ≤ 2`, Leibniz laws, naturality, supports; pushforward lemmas for formal chains (Hatcher §3.B) |
| `Affine` | 438 | 25 | affine simplices and affine chain maps in `Δᵖ × Δ^q` and `Δᵖ × (Δ^q × Δʳ)`, compatibility with product maps and the swap (Hatcher §2.1/§3.B) |
| `Chain` | 595 | 33 | chain-level cross products in left degree 0, 1, 2 (`crossProductEdge`, `crossProductTriangle`), naturality, affine computation, the Leibniz rule `∂(a×b) = ∂a×b + (-1)^p a×∂b` (Hatcher §3.B) |
| `HomologyDescent` | 56 | 5 | a map on cycles vanishing on boundaries descends to homology (Hatcher §2.1; generic over `ChainComplex (ModuleCat.{u} ℤ) ℕ`) |
| `Homology` | 308 | 16 | `crossProductHomology : H₁(X) ⊗ Hₙ(Y) → H_{n+1}(X × Y)` by double descent, computation on classes, degenerations at `n = 0` (Hatcher §3.B, `p = 1`) |
| `Swap` | 778 | 42 | graded commutativity `T_#(a×b) = (-1)^{pq} b×a` for `(1,1)`, the mixed `(2,1)/(1,2)` swap, and `crossProductHomologyTwoOne : H₂ ⊗ H₁ → H₃` defined through it (Hatcher §3.B) |
| `Associator` | 835 | 38 | associativity `(a×b)×c = a×(b×c)` for three 1-classes via the associator homotopy; cyclicity (Hatcher §3.B) |
| `Naturality` | 71 | 3 | naturality `(f×g)_#(a×b) = f_#a × g_#b`; `(pr₂)_#(a×b) = 0` (Hatcher §3.B) |

Total 4055 source lines in 218 units (216 public, 2 private), each moved exactly once.

Import graph: `Multilinear` ← `Formal`, `Affine` ← `Chain` (+ `CrossInsert`) ← `Homology`
(+ `HomologyDescent`) ← `Swap` ← `Associator`; `Naturality` ← `Homology`. `Multilinear` imports
`Chains`, `CircleProduct`; `HomologyDescent` imports `Chains`, `ModuleHomology`; so the facade's
transitive imports still contain the original four.

### How the tool was run

1. `44609e2b` — whitespace normalisation of the source first: 121 blank lines separating a
   `/-- … -/` docstring or `@[simp]` line from its declaration (all in the second half) removed;
   `git diff --ignore-blank-lines` empty. Reason: `split_module.py`'s upward extension of a unit stops
   at a blank line, so those docstrings and `attribute [local instance] … in` prefixes would have
   become context copied into every piece (observed on a trial run). Line map in `cross/linemap.json`.
2. Dump used to anchor the tool: `cross/dump_mod.jsonl`, a module-only dump of the seeded base
   `.olean` (`lake env lean-agent-ide dump Lib.AlgebraicTopology.SingularHomology.CrossProduct
   --modules Lib.AlgebraicTopology.SingularHomology.CrossProduct`), produced while the shared
   `dump_head.jsonl` was still running; its 318 rows agree with `dump_head.jsonl`'s rows for the
   module in names, ranges and `typeHashPublic` (checked, `cross/PROGRESS.md`). Ranges shifted
   through the line map (`cross/shift_dump.py` → `dump_mod_shifted.jsonl`).
3. Nine tool runs on the same (normalised) source, one piece moved per run, the keep file
   discarded: `cross/<Piece>.receipt.json`. Checks: the nine runs see the same 218 units; every unit
   is moved by exactly one run; every unit's `sha256` equals the hash of the source lines it names;
   no declaration line is left uncovered (85 uncovered non-blank lines = header, imports, module
   docstring, `@[expose] public noncomputable section`, `universe u`, `### ` headers, `section`/`open
   SingularHomology`/`end`). Context edits per piece (`cross/assemble.py`): piece module docstring,
   piece imports, own `### ` headers, empty `section … end` and unused `universe u` dropped.

## `Hopf/Proof` moves: none

Closure over `dump_head.jsonl` (`cross/closure.py` → `cross/closure.json`): of the 218 ranged
declarations, 207 are used, directly or transitively through this module, by a constant of another
`Lib` module and must stay; the 11 with no other-`Lib` user are `@[simp]` `_apply` lemmas
(`integerBilinearFlip_apply`, `integerBilinearPostcompose_apply`, `integerBilinearPrecompose_apply`,
`integerBilinearRightApply_apply`, `integerTrilinearPostcompose_apply`,
`integerTrilinearPrecompose_apply`, `crossProductAssociatorDefect_apply`,
`crossProductTwoOneCycles_val`, `zeroSimplexValue_comp`, `prodSwap_productAffineSimplex`) used
through `simp` (invisible to `uses`) and the instance `integerTensorModule`. None of the file is
project material in the sense of rule 3 (no dimension-6 hypothesis, no `Hemisphere.Sphere 2`, no
`mo1973`, no W4W1 index machinery): the second half is graded commutativity, associativity and
naturality of the cross product, Hatcher §3.B for `p = q = 1`, so it was renamed into
`SingularHomology` (the judgement's suggestion) rather than moved.

## Renames (`cross/rename.txt`, 115 lines `<new> <old>`)

`PeriodTorusHigherHomology.<x>` → `SingularHomology.<x>` for the 115 declarations of the second
half (113 public, 2 private: `triplePostcomp`, `triplePrecompLast`). No `SingularHomology.<x>`
existed for any of them (checked over `Lib`, `Hopf`), no other file defines these names, no
`open PeriodTorusHigherHomology`. Consumers: `Lib/AlgebraicTopology/SingularHomology/Pontryagin.lean`
(5 qualified uses), `Hopf/Proof/LCP/IntegralHomology.lean` (4), `Hopf/Proof/LCP/CuspFilling.lean` (1),
and one unqualified use inside a `PeriodTorusHigherHomology.*` declaration in
`Hopf/Proof/LCP/Specialization.lean:3258` (found by the `Solution` build, commit `f6b68450`).
`mo1973`: none in the base — `triplePostcomp_mo1973_13949`/`triplePrecompLast_mo1973_13950` were
already renamed in round 7 (`Lib/reports/round-7/names/rename.txt` l. 26–27).

## Universe lifts: none

Every `{X Y : Type}` declaration is pinned by `SingularChains.Chains (X : Type)`; the `{M : Type}`
of `chainBilinearLift`/`chainTrilinearLift`/`chainBilinearMap_ext`/`chainTrilinearMap_ext` is pinned
by `SingularChains.chainLift … {M : Type}`; the formal-chain and bilinear declarations are already
`Type*`; `HomologyDescent` is already `ModuleCat.{u}`.

## Docstrings

216 public declarations in the pieces, 216 with a docstring (computed by script over the pieces);
0 added this wave (the judgement's "0 missing" holds). Each piece has a module docstring.

## Checks (verbatim)

```
$ lake build -j3 …            → error: unknown short option '-j'   (lake 5.0.0; run without)
22:00:07 $ lake build Lib
Build completed successfully (9155 jobs).                                  exit 0
22:00:11 $ lake build Solution S6Shortcuts S6 Challenge
Build completed successfully (9207 jobs).                                  exit 0
22:11:05 $ lake build Lib.AxiomAudit Hopf.Proof.AxiomAudit
Build completed successfully (9157 jobs).                                  exit 0
   3302 `depends on axioms` lines; distinct sets: {propext, Classical.choice, Quot.sound},
   {propext, Quot.sound}, {propext}; 12 `does not depend on any axioms`; `sorryAx` absent.
22:11:26 $ python3 scripts/lib_stock_census.py --check
stock declarations under Hopf/: 123  …  ratchet PASS: 123 <= baseline 1648        exit 0
$ grep -rn '^import Hopf' Lib/ --include='*.lean'          → empty
   (without --include it hits only pre-existing text in Lib/docs/*.md and Lib/docs/logs/*.txt)
```
Log: `cross/checks2.log` (scratch); the piece builds after each step: `build1.log`, `build2.log`,
`build3.log` (all `done 0`). Tip at the time of the checks: `f6b68450`.

`lake` 5.0.0 (Lean 4.33.0) has no `-j` option (`lake build -j3 …` → `error: unknown short option
'-j'`); the pieces were built one module at a time (`cross/build1.sh`…`build3.sh`), the library
targets with lake's default parallelism.

## envdiff

`lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib --rename cross/rename.txt` after the
last edit (38 256 constants) against `dump_head.jsonl` (38 248):

```
constants before 38248 after 38256; lost 60 added 68, of which source declarations: 0 0;
names with changed type 3, of which source: 0; ambiguous module changes: 0;
module moves (source declarations, 1-to-1):
  CrossProduct -> CrossProduct.Multilinear 30, .Formal 26, .Affine 25, .Chain 33,
  .HomologyDescent 5, .Homology 16, .Swap 42, .Associator 38, .Naturality 3      (= the plan, 218)
VERDICT PASS
```

Source declarations: moves only. The 60 / 68 / 3 auxiliaries (not judged): 50 / 57 / 2 `_proof_n`
(re-abstracted per new module), 3 / 3 / 1 equation lemmas realized where first used
(`crossProductHomology.eq_1` …), 4 / 4 `_abel_…` tactic auxiliaries, 1 `match_n`, and the three
generated companions `formalAssociatorHomotopy._f`, `._sunfold`, `._unsafe_rec` of the structural
recursion, which appear as lost (old name) and added (new name) because the rename map covers
source names only. Files: `cross/envdiff.json`, `cross/envdiff.txt`.

## Left

* Left degree fixed to 1 and 2 (`crossProductEdge`, `crossProductTriangle`, `crossProductHomology`,
  `crossProductHomologyTwoOne`), the `Δ¹×Δⁿ`/`Δ²×Δⁿ` triangulations instead of Hatcher's shuffle
  formula, graded commutativity/associativity only for 1-classes: statement changes, out of scope
  for this wave; stated in every module docstring.
  `grep -n "crossProductHomology (X Y : Type)" Lib/AlgebraicTopology/SingularHomology/CrossProduct/Homology.lean`
* `HomologyDescent` (`homologyBoundaries`, `homologyLinearMap_ext`, `homologyBoundaries_le_ker`,
  `homologyDesc`, `homologyDesc_cycleClass`) belongs in
  `Lib/AlgebraicTopology/SingularHomology/ModuleHomology.lean` over any ring (judgement finding);
  kept as its own piece to avoid appending to a file the MayerVietoris agent may also touch and
  because the generalisation is a statement change.
  `grep -n "^def SingularHomology.homologyDesc " Lib/AlgebraicTopology/SingularHomology/CrossProduct/HomologyDescent.lean`
* `integerBilinearRightApply`, `integerBilinearFlip`, `integerBilinearPostcompose`,
  `integerBilinearPrecompose` and the trilinear versions re-implement `LinearMap.flip`,
  `LinearMap.compl₂`, `LinearMap.lcomp`/`compr₂` for `ℤ`; `integerLinearMapModule`,
  `integerTensorModule` are elaboration residue (a `Module ℤ` diamond). Not deleted (this wave
  deletes nothing); twins named in `Multilinear.lean`'s docstring.
  `grep -n "^def SingularHomology.integer" Lib/AlgebraicTopology/SingularHomology/CrossProduct/Multilinear.lean`
* `formalMap_comp`, `formalMap_comp_apply`, `formalMap_id_apply`, `formalMap_prod_swap` are generic
  `SingularMayerVietoris.formalMap` facts (now in `Formal.lean`); their home is the MayerVietoris
  formal-chain module, being split by another agent.
  `grep -n "^theorem SingularHomology.formalMap_\(comp\|id\|prod\)" Lib/AlgebraicTopology/SingularHomology/CrossProduct/Formal.lean`
* Universe: all space-indexed declarations stay at `Type` (pinned by `SingularChains.Chains`,
  `SingularChains.chainLift`); no lift possible in this file.
  `grep -c "(X Y : Type)" Lib/AlgebraicTopology/SingularHomology/CrossProduct/Chain.lean`
* `open Set Function Filter Manifold Topology` / `open scoped BigOperators TensorProduct` kept in
  every piece as original context; not trimmed.
  `grep -ln "^open Set Function Filter Manifold Topology" Lib/AlgebraicTopology/SingularHomology/CrossProduct/*.lean`
