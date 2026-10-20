# Wave 1 — `residue`: the fix list of `REVIEW-FIX.md` §3 and the residue of `MERGE.md` "Left"

Branch `wave1/residue`, base `lib/integration` at `e669bc93`, worktree `/home/goblin/hopf-w1-residue`.
Not a monolith split: receipt-text corrections, one docstring, one universe lift, the manuscript-label
sweep with the wider patterns, three citation numbers, two duplicate imports.  Scratch (kept):
`/home/goblin/.claude/jobs/06995e68/tmp/wave1/residue/`; copies of the check artefacts in
`Lib/reports/wave-1/residue/`.

## 1. Items

| item | what | commit |
|---|---|---|
| (a) | receipt-text corrections in `fixes/p02.md` (two sentences), `fixes/p0304.md`, `fixes/p10.md`, `fixes/p0708.md`, `round-7/packets/RECEIPT-08.md` item 7 — each in place, the original sentence quoted in a "(corrected 2026-09-27: …)" parenthetical | `90e5d593` |
| (g) | `fixes/names-dfiles.md`: `Hopf/Proof/AxiomAudit.lean` is built by explicit module target only (not in `defaultTargets`, imported by nothing) | `40a952ad` |
| (b) | `CleanStrips.lean` docstring of `exists_clean_bigon_boundary_neighborhood`: clauses of the conclusion listed first (`f`, open `W`, `ContMDiffOn`/`InjOn`/immersion on `W`, `f p ∉ S ∪ T` on `W ∩ interior (bigon h)`, compact closed `C ⊆ W` with `frontier (bigon h) ⊆ interior C`, closed embedding on `C`, `f p ∉ S ∪ T` on `bigon h ∩ C` off the frontier, `a`/`b` on the edges, germs `k.map ∘ lowerStripCoordinates`/`l.map ∘ upperStripCoordinates`); "meets the two sheets only there" replaced by the two bigon-side clauses and the sentence "Only the bigon side is constrained …", as `af11d3a2` did for `CleanBigonBoundary` | `28c0db0b` |
| (c) | `PositivePrimitives.lean`: `dualHomotopyEquiv`'s `{K L : ChainComplex (ModuleCat.{0} ℤ) ℕ}` → `ModuleCat.{u}` (`universe u w` already declared); proof body unchanged; `example` at `u = 0` below | `f5eed53b` |
| (f) | `Hopf/SphereTopology.lean`, `Hopf/Proof/SphereTopology.lean`: second `import Lib.Algebra.Module.IntegerPresentation` dropped | `04a2da09` |
| (e) | the three citation numbers — see §4; `p09.md`/`p0708.md` state one confidence for Bredon III Thm. 1.1 | `837c94e0` |
| (d) | manuscript-label sweep — see §3; one commit per file | `6f4547a6`, `0a36517a`, `1b8b2259`, `3f5009da`, `0c7c9688`, `1e83f00e`, `2ff009cd`, `1cddb83b` |

Docstrings edited (computed from `git diff -U0 e669bc93 HEAD`, counting distinct `/-- … -/` / `/-! … -/`
blocks that contain a changed line): 48 — `Cohomology/DerivedGlobalSections.lean` 17,
`Cech/DerivedGlobalSections.lean` 13, `Cech/Ext.lean` 7 (5 + 2 in the last commit), `Injective/Ext.lean` 4,
`LocalContributions.lean` 3, `Straightening.lean` 1, `CoveringDimension.lean` 1, `CleanStrips.lean` 1,
`ComparisonPositive.lean` 1.  Non-docstring source lines changed: 3 (the lift, the two import lines).
No statement changed; no `sorry`/`axiom`/`admit`; nothing under `Lib/reports/` or `Lib/reviews/` edited
beyond the files the assignment names and this receipt.

## 2. The lift (item c)

`dualHomotopyEquiv` (private, `PositivePrimitives.lean:72`) now has `levelParams [u, w]`:

```
dualHomotopyEquiv.{u_1, u_2} : (A : AddCommGrpCat.{u_2}) →
  {K L : ChainComplex.{u_1, u_1 + 1, 0} (ModuleCat.{u_1, 0} ℤ) ℕ} → HomotopyEquiv K L →
    HomotopyEquiv (dualComplex.{u_1, u_2} A L) (dualComplex.{u_1, u_2} A K)
```

Checked in `residue/LiftCheck.lean` (`lake env lean`, exit 0; output `LiftCheck.out`).  The private name is
found by a `run_cmd` scan of `env.constants` (suffix `SingularCochains.dualHomotopyEquiv`) and the two
examples are elaborated by `elabCommand` with that identifier:

(Corrected 2026-10-02: the first example was introduced as "the old statement at u = 0, proved by
the lifted constant"; it is the special case `w = 0` of that statement, since it takes
`(A : AddCommGrpCat.{0})` where the base statement had `(A : AddCommGrpCat.{w})`. The lift is still
the old statement at `u = 0`: the printed type above, `(A : AddCommGrpCat.{u_2}) → …`, is the base
type with `u_1 = 0`. Review `Lib/reports/wave-reviews/W1.md`, finding 12.)

```lean
-- the old statement at u = 0, proved by the lifted constant
example (A : AddCommGrpCat.{0}) {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (e : HomotopyEquiv K L) :
    HomotopyEquiv (dualComplex A L) (dualComplex A K) := dualHomotopyEquiv A e
-- the lift is real
example (A : AddCommGrpCat.{0}) {K L : ChainComplex (ModuleCat.{1} ℤ) ℕ} (e : HomotopyEquiv K L) :
    HomotopyEquiv (dualComplex A L) (dualComplex A K) := dualHomotopyEquiv A e
```

The one consumer, `pointCochainHomotopyEquiv`, stays at `u = 0` (`chains Unit`).  `.{0}` pins in
`PositivePrimitives.lean`: 9 → 8; in `Lib/**/*.lean`: 269 → 268 (`git grep -o '\.{0}' -- 'Lib/**/*.lean' | wc -l`).

## 3. Sweep (item d)

Patterns over `Lib/**/*.lean` at the base: `\bC[0-9]+[a-z]?\b` 21 hits, `\bM[0-9]+` 24, `textbook lines` 6,
`textbook` (case-insensitive) 64 in 27 files.  At the tip:

```
git grep -nE '\bC[0-9]+[a-z]?\b|\bM[0-9]+|textbook lines|textbook [0-9]' -- 'Lib/**/*.lean'
Lib/AlgebraicTopology/Hurewicz/Naturality.lean:64:* `Lib/docs/C14-NATURALITY.md` (typed ledger).
Lib/GroupTheory/FreeGroup/Invariant.lean:44:    | C1 => simp
Lib/Topology/Homeomorph/DiskCube.lean:47:* `Lib/docs/C15-DISKCUBE.md` (typed ledger and extraction provenance).
```

The `C14`/`C15` hits are the doc paths that stay by assignment; `C1` in `Invariant.lean:44` is a
constructor name in a `match` arm, not a label.

Rewritten (label → mathematics or section reference):

| file | labels removed | rewritten as |
|---|---|---|
| `Topology/Sheaves/Cohomology/Cech/DerivedGlobalSections.lean` | `M13`, `C29i`, `C30` ×7, "comparison statement (4)" ×2, "lines 1864–1878" | the two-sided Čech/derived comparison; the forward comparison named by its constant `cechToDerivedGlobalSections`; "Čech cohomology and derived global sections agree in every degree on a paracompact Hausdorff space"; a pointer to the file's own section |
| `Topology/Sheaves/Cohomology/DerivedGlobalSections.lean` | `M00-D` ×4, `D02` ×2, `M09` ×3, `M10` ×10, `C29f`, `C29g` ×3, "1600–1607", "1606–1607" | right-derived delta functor of global sections (`Lib.CategoryTheory.Abelian.CohomologicalDeltaFunctor.RightDerived`, `Functor.rightDerived n`); `κ⁻¹ ∘ ε` named by `extFunctorObjIsoDerivedGlobalSections_zero`; tags dropped where the sentence already states the fact |
| `Topology/Sheaves/Cohomology/Cech/Ext.lean` | `C29h` ×3, "textbook lines 1831–1849", "1835–1836" ×2, "1837–1838" ×2, "1850–1858, 1860–1862", "1850–1856, 1858–1862" | the two comparison morphisms between Čech cohomology and Ext from the constant integer sheaf |
| `CategoryTheory/Abelian/Injective/Ext.lean` | "textbook lines 1634–1639" ×2, "1640–1648", "1647–1648" | Ext by an injective resolution, cf. Weibel §2.5, §2.7 (the module docstring's reference) |
| `AlgebraicTopology/SingularHomology/LocalContributions.lean` | `CENTER_NATIVE_H5_INJECTIVITY_TEXTBOOK.md` (HI1–HI4, HI5–HI6), `CENTER_NATIVE_CONNECTING_KERNEL_TEXTBOOK.md` (CK1–CK4) — files that exist nowhere in the repository | Mayer–Vietoris exactness at the ambient term |
| `AlgebraicTopology/Hurewicz/Straightening.lean` | "(textbook §8)" | dropped; the sentence describes the construction |
| `Topology/Sheaves/Cohomology/CoveringDimension.lean` | "theorem (5) of textbook CD07" | the vanishing theorem of dimension theory for sheaf cohomology, cf. Godement II §5 |

Plain `textbook` at the tip: 25 hits in 21 files.  Four are in the monolith
`AlgebraicTopology/Hurewicz/CubeChainDecomposition.lean` (see "Left").  The other 21 are the English word
for standard material ("the textbook Kronecker evaluation map", "there is no textbook counterpart",
"the textbook hypothesis is paracompactness", …), not manuscript references; reproduce with
`git grep -niE 'textbook' -- 'Lib/**/*.lean' | grep -v CubeChainDecomposition`.  Left as they are.

## 4. Citations (item e)

| file:line | item | decision | confidence, reason |
|---|---|---|---|
| `CategoryTheory/Abelian/CohomologicalDeltaFunctor/Effaceable.lean:19` | Weibel, Exercise 2.4.5 | kept | sure: Ex. 2.4.5 is the effaceable-implies-universal exercise (Grothendieck's criterion), cited next to Thm. 2.4.7 and Hartshorne III.1.3A, which state the same result |
| `Topology/Sheaves/SingularCochainSheaf/ComparisonPositive.lean:20` | Godement II.3.9 | demoted to "cf. Godement, *Topologie algébrique et théorie des faisceaux*, II.5.10" | not sure of II.3.9 (Godement II §3 is the flasque-sheaf section); II.5.10 is the section pointer `ConstantSheafH1.lean:24` already uses for the same comparison statement — fairly sure, not checked against the book |
| `Topology/Sheaves/SingularCochainSheaf/GlobalUnitPredicates.lean:17` | Bredon, *Sheaf Theory* III Thm. 1.1 | kept | sure: the paracompact-HLC comparison of sheaf cohomology with constant coefficients and singular cohomology; the docstring describes the two steps of its proof |

`p09.md` (finding 4) and `p0708.md` (packet-08 finding 8) now both say: Bredon III Thm. 1.1 — sure;
`p09.md`'s "III §1" demotions were over-cautious, not wrong, and stay (section references are permitted).
The optional restoration of "III Ex. 8.1 (Leray)" in `FiniteClosedPushforward/AcyclicResolution.lean`
(REVIEW-FIX §3) was not done: the shipped "cf. III.8" is a permitted section reference.

## 5. Checks

Lake 5.0.0 (`lake --version`: `Lake version 5.0.0-src+d8b1897 (Lean version 4.33.0)`) has no `-j`
option (`error: unknown short option '-j'`), so the builds ran with Lake's default job count.  Scripts
`residue/build1.sh`, `residue/build2.sh`, logs `build1.log`, `build2.log`, `axiomaudit.out`.

```
lake build <the 12 edited modules>        Build completed successfully (8922 jobs).   (build1, step modules)
lake build Lib                            Build completed successfully (9146 jobs).   (build1)
lake build Lib.AxiomAudit                 Build completed successfully (9146 jobs).   (build1; 3298 axiom
                                          reports + 12 "does not depend on any axioms"; sets ⊆ {propext,
                                          Classical.choice, Quot.sound}; sorryAx 0)
lake build Solution S6Shortcuts S6 Challenge   Build completed successfully (9198 jobs).   (build1)
lake build Lib.Topology.Sheaves.Cohomology.Cech.Ext   Build completed successfully (2234 jobs).   (build2,
                                          after the last commit 1cddb83b)
lake build Lib                            Build completed successfully (9146 jobs).   (build2)
python3 scripts/lib_stock_census.py --check    ratchet PASS: 123 <= baseline 1648
grep -rn '^import Hopf' --include='*.lean' Lib/    0 hits
```

The 12 edited modules: `Lib.Geometry.Manifold.Whitney.CleanStrips`,
`Lib.AlgebraicTopology.SingularCochains.PositivePrimitives`, `Lib.AlgebraicTopology.Hurewicz.Straightening`,
`Lib.AlgebraicTopology.SingularHomology.LocalContributions`, `Lib.CategoryTheory.Abelian.Injective.Ext`,
`Lib.Topology.Sheaves.Cohomology.Cech.DerivedGlobalSections`, `Lib.Topology.Sheaves.Cohomology.Cech.Ext`,
`Lib.Topology.Sheaves.Cohomology.CoveringDimension`, `Lib.Topology.Sheaves.Cohomology.DerivedGlobalSections`,
`Lib.Topology.Sheaves.SingularCochainSheaf.ComparisonPositive`, `Hopf.SphereTopology`,
`Hopf.Proof.SphereTopology`.  `Hopf.Proof.AxiomAudit` was not built (no Hopf declaration touched; the two
Hopf files lost an import line only, and `Solution` builds them).

## 6. Envdiff

Base `dump_head.jsonl` (38,248 constants; `dump_head.err` ends `done 0`), after-dump `residue/dump_after.jsonl`
(`lake env lean-agent-ide dump Solution Lib --modules Hopf,Lib` after the last commit `1cddb83b`, all builds
finished first; 38,248 constants; `dump_after.err` ends `done 0`).  A first after-dump started before
`1cddb83b` was killed by its exact pid and discarded.

```
python3 /home/goblin/lean-agent-ide/tools/envdiff.py dump_head.jsonl dump_after.jsonl --receipt envdiff.json
constants before 38248 after 38248 (keys 38146 38146 )
lost 3 added 3 of which source declarations: 0 0 ; names with changed type 3 of which source: 1
  PROOF-NAMING AlgebraicTopology.SingularCochains.dualHomotopyEquiv
auxiliary lost/added/changed (not judged): 3 3 2
module moves (source declarations, 1-to-1):
ambiguous module changes: 0
auxiliary constants that changed module: 0
VERDICT PASS
```

Reconciled name by name: the 3 lost / 3 added rows are the changed-type constants themselves (the tool lists
a changed-type constant as lost and added) — `dualHomotopyEquiv` (source, the lift of item c) and its two
auxiliaries `dualHomotopyEquiv._proof_1`, `._proof_2` (re-elaborated at the new universe).  0 source
declarations lost or added, 0 moves, exactly one changed source type.  Files `residue/envdiff.json`,
`residue/envdiff.txt`.

## 7. Left

- `AlgebraicTopology/Hurewicz/CubeChainDecomposition.lean` is a wave-1 monolith (another agent); four
  manuscript references there: `git grep -nE 'textbook' -- Lib/AlgebraicTopology/Hurewicz/CubeChainDecomposition.lean`
  → l.968 "(textbook §10.3)", l.2006 "(textbook §10.3)", l.2041 "of the lane's textbook (§9, L5)",
  l.2107 "(textbook §9)".
- `Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean` (monolith, another agent) still imports
  `Lib.Algebra.Module.IntegerPresentation` twice:
  `grep -c '^import Lib.Algebra.Module.IntegerPresentation' Lib/Geometry/Manifold/Morse/SurgeryCollapse.lean` → 2.
- Chain-side `.{0}` pins that stay (forced by `chains`/`ModuleCat.of ℤ ℤ`): 8 in `PositivePrimitives.lean`
  (`grep -c '\.{0}' Lib/AlgebraicTopology/SingularCochains/PositivePrimitives.lean`), 2 `ULift.{0} ℤ` in
  `Vanishing.lean`, 13 in `SingularCochainSheaf/PrimitivesH1.lean` — unchanged from MERGE.md "Left".
- "Warner 5.32" kept deliberately by `p10.md` in `Pullback/FiniteClosedPositive.lean`,
  `Pullback/ComparisonH1.lean`, `ComparisonPositive.lean` (`git grep -n 'Warner.*5\.32' -- 'Lib/**/*.lean'`).
- The 21 generic `textbook` hits of §3 (English usage; no label) — reproduce with the grep there.
- `p09.md`'s five "Bredon III §1" demotions (`GlobalPatch.lean`, `GlobalPatchLocal.lean`, `ComparisonH1.lean`
  ×2, `ComparisonPositive.lean` ×2) could be restored to "III Thm. 1.1"/"III Prop. 1.1" now that the
  theorem number is agreed; not done (section references are permitted; "III Prop. 1.1" stays unverified).
- Optional "III Ex. 8.1 (Leray)" restoration in `FiniteClosedPushforward/AcyclicResolution.lean` (§4).
- `w4-w1-solution` reroute of `SphereTwo` (MERGE.md "Left"), the lost per-packet round-7 envdiffs — untouched,
  not this task.

## 8. Commits

`e669bc93..HEAD` on `wave1/residue`, one per item (sweep: one per file), all with the two trailers:

| commit | subject |
|---|---|
| `90e5d593` | `Lib/reports: correct five fix-round receipts in place (REVIEW-FIX §3)` |
| `40a952ad` | `Lib/reports: names-dfiles.md — AxiomAudit built by explicit target only` |
| `28c0db0b` | `Lib/Geometry/Manifold/Whitney/CleanStrips.lean: docstring of exists_clean_bigon_boundary_neighborhood` |
| `f5eed53b` | `Lib/AlgebraicTopology/SingularCochains/PositivePrimitives.lean: lift dualHomotopyEquiv to .{u}` |
| `04a2da09` | `Hopf/SphereTopology.lean, Hopf/Proof/SphereTopology.lean: drop duplicate import` |
| `837c94e0` | `Lib/Topology/Sheaves/SingularCochainSheaf/ComparisonPositive.lean: demote Godement II.3.9` |
| `6f4547a6` | `Lib/Topology/Sheaves/Cohomology/Cech/DerivedGlobalSections.lean: drop manuscript labels M13, C29i, C30, (4)` |
| `0a36517a` | `Lib/Topology/Sheaves/Cohomology/DerivedGlobalSections.lean: drop manuscript labels M00-D, D02, M09, M10, C29f, C29g` |
| `1b8b2259` | `Lib/Topology/Sheaves/Cohomology/Cech/Ext.lean: drop manuscript labels C29h and line ranges` |
| `3f5009da` | `Lib/CategoryTheory/Abelian/Injective/Ext.lean: drop manuscript line ranges` |
| `0c7c9688` | `Lib/AlgebraicTopology/SingularHomology/LocalContributions.lean: drop references to *_TEXTBOOK.md files` |
| `1e83f00e` | `Lib/AlgebraicTopology/Hurewicz/Straightening.lean: drop "(textbook §8)"` |
| `2ff009cd` | `Lib/Topology/Sheaves/Cohomology/CoveringDimension.lean: drop "theorem (5) of textbook CD07"` |
| `1cddb83b` | `Lib/Topology/Sheaves/Cohomology/Cech/Ext.lean: drop two remaining manuscript line ranges` |
| (last) | this receipt with `Lib/reports/wave-1/residue/{LiftCheck.lean,LiftCheck.out,envdiff.json,envdiff.txt,build1.log,build2.log}` |
