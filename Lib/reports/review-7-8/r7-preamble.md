# Review of Lib/reports/round-7/preamble/RECEIPT.md

**Verdict: ACCEPT WITH FINDINGS** — the end state is sound (every deletion is a whole preamble
line, the four restored files carry the option at head, envdiff shows 0 source declarations
lost/added/changed, no hygiene issue), but the receipt misdescribes its own method and its own
envdiff: the compile-only `open scoped` minimisation is unsound in the files it was run on
(all 96 have `autoImplicit` on), the SquareRoot type change it "pinned" was an auto-bound
implicit, not an instance path, and the 410-constant envdiff churn is not all notation artifacts.

## Findings

1. **[wrong receipt] [incomplete] The `open scoped` minimisation criterion ("keep the drop only
   when the file still compiles on its own") is not sound in these files, and the receipt does
   not say so.** `lakefile.toml` sets no `leanOptions`; Lean v4.33.0 defaults `autoImplicit`
   to true (checked: `example (α : Type u) : Type u := α` compiles with bare `lean`, no
   `universe u`). 221 of the 446 `Lib/**/*.lean` files at the branch tip carry no
   `set_option autoImplicit false` — including **all 96** category-(b) files and **all 90**
   category-(c) files. In such a file, dropping a namespace whose scoped notation is an
   identifier-like token (`ω`, `ℍ`, `𝔻`, `𝓤`, `𝒟`, `Ι`, `𝟙`, `𝟭`, `conj`, `SL(`, `GL(`)
   does not break the build: the token becomes an auto-bound implicit in the signature.
   Demonstrated in `/home/goblin/hopf-lib-integration` (probe file
   `review-pass/r7-preamble/probe.lean`):
   ```
   theorem autoBoundDemo (f : ℝ → ℝ) (h : ContDiff ℝ ω f) : True := trivial   -- no open scoped ContDiff
   #check @autoBoundDemo   -- ∀ {ω : WithTop ℕ∞} (f : ℝ → ℝ), ContDiff ℝ ω f → True
   ```
   This is exactly what happened to `AnalyticRootCover.exists_holomorphic_square_root_upperHalfPlane`
   (`Lib/Analysis/Complex/SquareRoot.lean:758` at base: `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω r`): with
   `ContDiff` dropped the theorem silently acquired a universally quantified `{ω : WithTop ℕ∞}`.
   The receipt files this under "instance path, then `ContDiff`" and never names the
   mechanism. The only thing that made the result safe was the final type-hash envdiff, which
   did catch this one case. My own token scan of all 96 files at the branch tip (tokens of
   each dropped namespace, comments stripped) finds no remaining identifier-like scoped token
   in a file that dropped its namespace, and `#synth NatCast (Fin 3)` /
   `#synth Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2)` both fail globally, so the
   dropped `Fin.NatCast` / `EuclideanSpace` scoped instances cannot have been silently
   replaced. **Should happen:** the receipt must state that `autoImplicit` is on in these
   files, that compile-success is therefore not evidence of an unused namespace, and that the
   guarantee rests solely on the envdiff. (The brief's premise "autoImplicit is off repo-wide"
   is false for half of `Lib`.)

2. **[wrong receipt] [incomplete] The envdiff churn is misattributed and a definition body
   changed.** Receipt: "The 410 constants that disappeared are the notation artifacts of the
   137 deleted `local notation` … lines and their unexpanders." `envdiff.json`: `lost` (20) =
   6 notation-artifact names (`«term_≫ₚ_»`, `«term_∣[_]_»`, two `_aux_…macroRules…`, two
   `_aux_…unexpand…`, each aggregated over ~69 modules) **plus 14 `_proof_N` auxiliaries of
   `PeriodTorusHigherHomology.formalAssociatorDefect` and
   `PeriodTorusHigherHomology.triplePostcomp_mo1973_13949`** in
   `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean`; `added` (15) and
   `changed_type_all` (14) are *only* those `_proof_` names. The branch diff of that file is
   the single line `-set_option maxSynthPendingDepth 3` (it never had the stock `open scoped`
   block). So removing the option changed the elaborated *value* of a `def`: at head,
   `formalAssociatorDefect._proof_2` / `_proof_3` are `SMulCommClass ℤ ℤ (…)` obligations
   discharged by `AddGroup.int_smulCommClass`, `_proof_5` the same class by
   `LinearMap.instSMulCommClass` (`#print`, probe.out lines 134–155); at base there was one
   `_proof_` fewer with different hashes. `SMulCommClass` is a `Prop`, so this is
   proof-irrelevant and benign, and `formalAssociatorDefect_apply` is still `rfl`. But it is
   direct evidence that `envdiff.py` compares types only and that removing
   `maxSynthPendingDepth` did change definition bodies — the same "instance path" class of
   change the receipt chose to *restore* when it showed up in four types. Arithmetic:
   411 notation artifacts (138 notations at base − 1 kept, × 3 constants) + 14 `_proof_` lost
   − 15 `_proof_` added = 410. **Should happen:** the receipt lists the `_proof_` churn, says
   why it is harmless (Prop instance), and states explicitly that definition values were not
   compared in the 104 files that lost the option.

3. **[wrong receipt] "All 90 hits were the stock line `universe u v`."** The branch diff
   deletes 89 × `universe u v` and 1 × `universe u v w` (`Lib/Topology/MappingTorus/Wang.lean`,
   commit `cd439ebf`). `w` is unused there as well (checked with my own regex), so the
   deletion is fine; the sentence is false. Also "233 `universe` commands in 230 files": the
   receipt's own regex matches 233 lines in **227** files at base (230 is the count of files
   with any line starting `universe`, including three docstring lines).

4. **[wrong receipt] (minor) The instance-path description does not match the file I
   checked.** Receipt: "synthesis of `NormedSpace ℝ ℝ` resolves through
   `NormedField.toNormedSpace` where the base resolved through
   `InnerProductSpace.toNormedSpace ∘ RCLike.toInnerProductSpaceReal`." At head,
   `@HolomorphicCousin.hasFDerivAt_cauchyGreen` (Cousin.lean, option restored) carries
   `@InnerProductSpace.toNormedSpace ℝ ℂ Real.instRCLike _ instInnerProductSpaceRealComplex`,
   i.e. the class is `NormedSpace ℝ ℂ` and the inner-product instance is
   `instInnerProductSpaceRealComplex`, not `RCLike.toInnerProductSpaceReal`. The claim may
   hold for Collar/Birth (`E = ℝ`); I did not spend the elaborations to check. The substantive
   claims — option present at head in exactly Cousin, SquareRoot, Collar, Birth (+ MorseLemma,
   SmoothFlow = 6/110), `changed_type_source` empty — are verified.

5. **[nit] Internal inconsistencies.** "49 keep one namespace, 16 keep two" is the
   pre-restoration distribution (JSON at head: 48 / 17 / 2 / 1), whereas the frequency table
   "ContDiff 51" is post-restoration (commit `5314b057` says 50). `Challenge.lean:42` — the
   `sorry` is at line 46 at base. "1565 single-file `lean` compiles" — no log is in the
   receipt directory, unverifiable.

## Claims checked

| claim | status | how |
|---|---|---|
| Whole-line deletions only; no import / `backward.*` / `maxHeartbeats` line touched; no declaration changed | verified | `git diff 46c22597 e401e75a^2 -- 'Lib/**/*.lean'`: added lines are 68 `open scoped …` lines only; deleted lines are 104 `set_option maxSynthPendingDepth 3`, 96×4 stock block lines, 89 `universe u v`, 1 `universe u v w`, 69 + 68 local notations, 359 blanks |
| `110 files changed, 68 insertions, 1074 deletions` | verified | `git diff --shortstat` |
| (a) 110 files carried the option, all with value 3; 108 edited; 2 restored (MorseLemma, SmoothFlow); 6 survive | verified | `git grep` at base (110, no other value); commit `4ffc57e2` stat (108 .lean files); `git grep maxSynthPendingDepth 39f1d12b -- Lib` = exactly the 6 files |
| (b) stock 4-line block verbatim in 96 files; 28 removed outright, 68 narrowed; 384 removed / 68 added | verified | `git grep -F` at base = 96; JSON has 68 entries, all with the block at base; 96−68 = 28; commit `5314b057` stat 412 del (384+28 blanks) / 68 new lines |
| Seven namespaces needed by no file | verified (as a compile fact) | JSON `keep` frequency; but see finding 1 for what "needed" means |
| `open Set Function Filter Manifold Topology` in 111 files, untouched | verified | `git grep -l` at base = 111; no such line in the diff |
| (c) rule found only stock lines; 90 files; no name used in a universe position | partly (see finding 3) | independent regex over the 90 base files: no `u`/`v`/`w` in `Type _`/`Sort _`/`.{}`/`max`/`+1` positions (6 regex hits inspected, all term variables named `u`/`v` after `Type*}`) |
| (d) 69 files, 137 lines, both stock lines; LoopSubdivision keeps `≫ₚ` because used | verified | `git grep` at base: 138 lines in 69 files, exactly the two stock forms; `≫ₚ` used at LoopSubdivision.lean:90,103,104,123,169; `∣[` used nowhere; tip has exactly 1 local notation left |
| Restorations: option in Cousin/Collar/Birth/SquareRoot; `ContDiff` re-added in SquareRoot; 9 added / 1 removed | verified | `git show 779accf3`; head lines Cousin:49, SquareRoot:42,46, Collar:59, Birth:51 |
| `ω` in the restored SquareRoot statement is `⊤` | verified | probe: `@Top.top (WithTop ENat)` at the `ContMDiff` argument |
| envdiff: 0 source lost/added/changed, VERDICT PASS | verified | `envdiff.json`: `changed_type_source`, `moves`, `ambiguous` empty; `lost`/`added` names all `_proof_`/`_aux_`/`term_` |
| "410 disappeared constants are notation artifacts" | refuted | finding 2 |
| `Solution`/`Lib` dump clash on `SpecialPeriods.Threefold.Star.Input` | verified | declared at `Lib/Topology/Gluing/OverBase.lean:217` and `Hopf/Proof/LCP/GlobalAssembly.lean:379` |
| Commit list, one commit per category + restoration + receipt; trailers | verified | `git log 46c22597..e401e75a^2`; all five work commits carry `Co-Authored-By` + `Claude-Session` |
| Hygiene: no `sorry`/`axiom`/`unsafe`/`native_decide`/`@[simp]`/`noncomputable`/`private` change; no `import Hopf` in `Lib/*.lean` | verified | added-line histogram of the diff; `git grep "import Hopf" 39f1d12b -- Lib` hits only `.md`/`.txt` |
| Later branches did not undo the restorations | verified | `git diff e401e75a^2 39f1d12b` on the four files touches only docstrings (SquareRoot) or nothing |
| Builds green (`lake build Lib`, `Solution …`, `Lib.AxiomAudit`), axiom set | not independently rebuilt | `build-summary.txt`; the integration copy at `39f1d12b` is built, which covers `Lib` at head only |

## Not checked

* The three other "instance path" types (Collar ×2, Birth) with `pp.explicit` — would need
  three more heavy elaborations; only the Cousin one was printed.
* Definition-value differences in the other 103 files that lost `maxSynthPendingDepth` (no
  tool; the envdiff does not hash values). The one case surfaced by the envdiff is benign.
* The 1565 single-file compiles and the three `lake build` runs (no logs; cannot rebuild).
* Whether `envdiff.py`'s type hash includes universe-parameter order (relevant to the 90
  auto-implicit files that lost `universe u v`; my regex found no use of the names, so moot).
* `triplePostcomp_mo1973_13949._proof_1` (private, name-mangled; `#print` by that name fails).

## Tool notes

* The receipt should record the `autoImplicit` state of every file it minimises by
  compile-success; better, run the minimisation with `-DautoImplicit=false` (or add the
  `set_option` first) so that a dropped identifier-like notation fails loudly.
* `envdiff.py` should hash definition values (at least for `def`/`abbrev`/`instance`) or the
  receipt must say it does not; "auxiliary … not judged" hides real information — the
  `_proof_` churn was the only trace that a body changed.
* The receipt's per-category tables were accurate; the lookup that took longest was mapping
  each `lost` entry to a cause. A one-line-per-lost-name reconciliation in the receipt would
  have made finding 2 unnecessary.
* The minimisation JSON should include the compile log path or hash per file and the
  `autoImplicit` flag; `open-scoped-minimized.json` has `error: ""` for every file, which
  carries no information.
