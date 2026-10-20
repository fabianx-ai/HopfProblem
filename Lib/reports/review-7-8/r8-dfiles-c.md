# Review of Lib/reports/round-8/dfiles-c/RECEIPT.md

**Verdict: ACCEPT WITH FINDINGS** — the three commits do what the receipt says (move, rename, docstrings; envdiff clean; twins verified), but the receipt's causal explanation of the "load-bearing" instance is wrong, its claim that the moved theorems "remain axiom-audited transitively" is false, and two Mathlib file attributions in the new docstrings are wrong.

Branch `r8/dfiles-c`, base `4e15a034`, tip `12232351^2` (= `ed7f768b`), 4 commits; after-state checked at `39f1d12b`.

## Findings

1. **[wrong receipt] [docstring] The stated cause of the instance-resolution gap is wrong; the "load-bearing" conclusion is right for the wrong reason.**
   Receipt §2 and the new module docstring of `Lib/Topology/Sheaves/Cohomology/AddCommGroup.lean` (head lines 28–36) say: "Typeclass resolution does not see through `CategoryTheory.Sheaf.H` to `Ext` in this development … Closing the gap is an upstream change to `Sheaf.H`."
   Reproduced with scratch files under `/home/goblin/.claude/jobs/06995e68/tmp/review-pass/r8-dfiles-c/` (`Probe.lean`, `Probe2.lean`, `Probe4.lean`), all `import Lib.Topology.Sheaves.Cohomology.AddCommGroup` with `attribute [-instance] CategoryTheory.Sheaf.instAddCommGroupH`:
   * `F : TopCat.Sheaf AddCommGrpCat.{u} X` — `#synth AddCommGroup (Sheaf.H F n)` **fails**, `#synth Add (Sheaf.H F n)` fails, and `Sheaf.H.map g 0 : H G 0 →+ H Q 0` fails with `AddZero (Sheaf.H G 0)`. So the instance really is load-bearing for `Lib` as written: **confirmed, not trusted.**
   * `F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}` (same `Sheaf.H`, same `J`) — `#synth AddCommGroup (Sheaf.H F n)` **succeeds** and prints `Ext.instAddCommGroup`. So `Sheaf.H` *is* seen through to `Ext`; Mathlib's own `H.map` is defined this way.
   * `F : TopCat.Sheaf …` again, with `set_option allowUnsafeReducibility true` + `attribute [local reducible] TopCat.Sheaf` — `#synth` **succeeds** (`Ext.instAddCommGroup`) and `H.map g 0` elaborates.
   * Trace (`Probe2.out`): the only relevant candidate `@Ext.instAddCommGroup` fails at `AddCommGroup (Sheaf.H F n) ≟ AddCommGroup (Ext ?m.12 ?m.13 ?m.14)` — the unifier, at instance transparency, cannot identify `TopCat.Sheaf AddCommGrpCat X` (Mathlib `Mathlib/Topology/Sheaves/Sheaf.lean:108`, a plain `nonrec def … deriving Category`) with `CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat`.
   The gap is Mathlib's `TopCat.Sheaf` being a non-reducible `def` while `Lib` feeds `TopCat.Sheaf`-typed objects to the site-level `Sheaf.H`; nothing about `Sheaf.H` needs an upstream change. The instance should stay (the packet's own alternative "fix the gap upstream if `Sheaf.H` genuinely fails" does not apply — it does not genuinely fail), but the docstring's "Typeclass resolution does not see through `Sheaf.H` to `Ext`" and "Closing the gap is an upstream change to `Sheaf.H`" should be replaced by the `TopCat.Sheaf`-reducibility explanation, and the receipt's "so this registration is load-bearing; closing the gap is an upstream change to `Sheaf.H`" is a mis-diagnosis. (A third option the receipt never considered: state the instance for `CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat` / make `Lib`'s sheaves site-typed; that is a design decision for the owner, not a finding against this packet.)

2. **[wrong receipt] "The declarations remain axiom-audited transitively: they are in the import closure of `Solution.lean`, whose `#print axioms` line is unchanged."** (receipt §1, `Lib/AxiomAudit.lean` bullet). `#print axioms` reports the axioms in the *dependency closure of the named constant*, not the import closure. Nothing in the `Solution` import graph references the four `…_of_homeomorph_sphereTwo` theorems (`git grep homeomorph_sphereTwo 39f1d12b` hits only the moved file itself; `Hopf/Proof/Final.lean` only imports the module, 1 hit = the import line), so `Solution.lean`'s `#print axioms 'Mathoverflow1973.mathoverflow_1973'` says nothing about them. After this branch the four theorems are axiom-probed by **nothing**. (By inspection the proofs use only `Lib` theorems, Mathlib, and `by decide`, so the practical risk is nil, but the receipt's justification is false and should say "no longer probed".) The "Left undone" bullet is honest about the missing home; the sentence quoted above contradicts it.

3. **[docstring] Two wrong Mathlib file attributions in the new docstrings.**
   * `AddCommGroup.lean` module docstring (head lines 22–26) and receipt §2: "`CategoryTheory.Abelian.Ext.instAddCommGroup` (`Mathlib/CategoryTheory/Abelian/GrothendieckCategory/HasExt.lean`)". The instance is `noncomputable instance : AddCommGroup (Ext X Y n)` at `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean:239`; `HasExt.lean` contains no `AddCommGroup` at all (it supplies the `HasExt` instance for Grothendieck abelian categories).
   * `SheafificationLocal.lean` module docstring `## References` (branch diff, and receipt §3): "`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso` (`Mathlib/Topology/Sheaves/Stalks.lean`)". It is at `Mathlib/Topology/Sheaves/Sheafify.lean:137`. (`germ_eq` is in `Stalks.lean:456`, correct; the packet made the same Stalks.lean error and the agent copied it.)
   The declaration names themselves are all correct (`isLocallySurjective_toSheafify` is an `instance` at `Sites/LocallySurjective.lean:302`; `TopCat.Presheaf.isLocallySurjective_iff` at `Topology/Sheaves/LocallySurjective.lean:64`).

4. **[incomplete] Consumer on `w4-w1-solution` will break and the receipt does not say so.** Receipt §1: "its manuscript consumers live on `w4-w1-solution`". Concretely `W4W1/CenterBaseCohomologicalDimension.lean:1` there is `import Lib.Topology.Sheaves.Cohomology.SphereTwo` (uses two of the four theorems at lines 43, 62), and that branch's `Lib.lean:416` and `Lib/AxiomAudit.lean:7419–7430` still carry the old module/probes. When `w4-w1-solution` meets this branch, that import must be rerouted to `Hopf.Proof.Topology.Sheaves.Cohomology.SphereTwo`. The receipt should list this as a pending reroute.

5. **[nit] Dead import.** `Hopf/Proof/Final.lean:165` imports the moved module solely so it keeps compiling; nothing in the `Solution` graph uses it. The receipt says this plainly ("The file had no consumer on this base"), so this is a design note, not a receipt error: on this branch the four theorems are dead code kept alive by an import, pending finding 4's reroute.

6. **[nit] Call-site count.** Receipt §2 / commit `d87ad506`: "All eleven call sites were updated". `git grep -c cohomologyAddCommGroup 4e15a034 -- Lib/` (excluding reports and the defining file) gives 12 occurrences in 7 files (AxiomAudit 2, CanonicalPositive 1, ConstantPointFibre 2, ResolutionTransgression 1, ConstantProductH1 2, ConstantProductPositiveFibreIndependence 2, ConstantSheafH1 2), i.e. 10 real call sites + 2 audit probes; the round-7 receipt says "ten". Every one is updated (no residue at head outside `reports/`), so only the number is off.

7. **[nit] Envdiff prose.** Receipt: "the one auxiliary constant is the `_proof_1` of the first of them" reads as the `_proof_1` of the first *theorem*; the dumps show it is `instAdditiveSheafOpens…_lib_1._proof_1`, the `_proof_1` of the first `local instance` (base: `_private.Lib.Topology.Sheaves.Cohomology.SphereTwo.0.instAdditive…_lib_1._proof_1`, after: `instAdditive…_lib_1._proof_1` under `Hopf.Proof…SphereTwo`).

## Claims checked

| claim | status | how |
|---|---|---|
| 4 commits, one per file plus receipt; messages describe the commits; trailers present | verified | `git log --format=full 4e15a034..12232351^2` |
| SphereTwo moved with statements byte-identical; 4 theorems + 2 `local instance`s + 1 aux | verified | `git diff 4e15a034 12232351^2` shows only header/docstring hunks in the moved file (similarity 78%); names in `dump_base.jsonl` module `Lib…SphereTwo` = names in `dump_after.jsonl` module `Hopf.Proof…SphereTwo` (7 lines incl. `_proof_1`) |
| Post-merge drift of the moved file | noted | `git diff 12232351^2 39f1d12b -- Hopf/Proof/…/SphereTwo.lean`: 4 lines, `integralSheaf` → `TopCat.ConstantSheaf.integralSheaf` (dup-sheaf's rename, applied by the merge); statements otherwise unchanged |
| `Lib.lean` line removed; no `Lib` file imports the moved module; `grep import Hopf Lib/` empty for `.lean` | verified | `git grep "Sheaves.Cohomology.SphereTwo" 39f1d12b` → only `Hopf/Proof/Final.lean:165`; `git grep "import Hopf" 39f1d12b -- Lib/` hits only `.md`/`.txt` docs |
| "`Hopf` lean_lib has no root module" | verified | `lakefile.toml` `[[lean_lib]] name = "Hopf"` without `roots`; no `Hopf.lean` in tree (`git ls-tree 39f1d12b`) |
| `Solution.lean` imports `Hopf.Proof.Final` | verified | `Solution.lean:59` |
| Four probes removed from `Lib/AxiomAudit.lean`, none anywhere else | verified (and see finding 2) | branch diff; `git grep homeomorph_sphereTwo 39f1d12b`; `git grep -l "print axioms" 39f1d12b -- Hopf/` → none |
| "remain axiom-audited transitively" | **refuted** | finding 2 |
| Rename `cohomologyAddCommGroup` → `instAddCommGroupH`, statement/binders/proof unchanged on the branch | verified | branch diff of `AddCommGroup.lean` (only the name and docstrings change); head is at `.{u}` via `pins` as MERGE.md §5 says |
| Old name absent at head, new name present, all call sites updated | verified (count off, finding 6) | `git grep cohomologyAddCommGroup 39f1d12b -- Lib/ Hopf/ Solution.lean` → only reports/reviews |
| Instance is load-bearing (deletion fails with `Add (Sheaf.H Q 0)` / `AddZero (Sheaf.H F n)`) | verified, cause **refuted** | `Probe.lean` (fails without it, explicit `Ext.instAddCommGroup` term elaborates), `Probe2.lean` (site-typed sheaf succeeds), `Probe4.lean` (reducible `TopCat.Sheaf` succeeds) — finding 1 |
| Round-7 names receipt records the same experiment | verified | `Lib/reports/round-7/names/RECEIPT.md:66` |
| Rename map: direction, 9 lines, symmetric difference of name sets | verified | `rename.txt`; after dump shows `_lib_1`/`_lib_2` names under the `Hopf.Proof…` module (only possible if the map fired); base dump has `_lib`, `_lib_1`, `_lib_2` unchanged |
| envdiff: 38593/38593, lost 0 / added 0 / changed 0, one 6-declaration module move, 1 aux moved, PASS | verified | `envdiff.json`; dump greps above |
| SheafificationLocal: documentation only, no declaration added/removed/renamed | verified | branch diff (docstrings and module docstring only) |
| SheafificationLocal docstrings correct vs. declarations | verified (names) / **refuted** (one file path, finding 3) | `sheaf` names its definiens (head: `(TopCat.Sheaf.sheafification X).obj P`, merge-adjusted); `unit` = `toSheafify (Opens.grothendieckTopology X) P`; `unit_stalk_isIso` proof term is `stalkFunctor_map_unit_toSheafify_isIso`; `unit_stalk_injective` = injective half. Mathlib names grepped in `.lake/packages/mathlib` |
| The three "proved" results (`exists_local_representative`, `germ_unit_eq_iff`, `exists_restriction_eq_of_germ_unit_eq`) have consumers in `Lib` | verified | `git grep -l SheafificationLocal 39f1d12b -- Lib/` → 6 modules besides the file and AxiomAudit |
| AddCommGroup docstring: `Sheaf.H` is by definition `Ext` (`Sites/SheafCohomology/Basic.lean`) | verified | Mathlib `Basic.lean:59` `abbrev H (n : ℕ) : Type w' := Ext ((constantSheaf J _).obj (of (ULift ℤ))) F n` |
| AddCommGroup docstring: instance file is `GrothendieckCategory/HasExt.lean` | **refuted** | finding 3 |
| SphereTwo docstring: general results named exist in `Lib` | verified | `Lib/Topology/Sheaves/Cohomology/CoveringDimension.lean:46`, `Lib/Topology/Dimension/SphereTwo.lean:37` |
| Godement II.5.12 is the covering-dimension vanishing theorem | plausible, not certain | from memory: Godement II §5.12 "Dimension cohomologique", Thm 5.12.1 (paracompact, dim ≤ n ⇒ H^q(X,F)=0 for q>n); no copy at hand |
| Packet's "l.8 imports ResolutionTransgression — unrelated" | packet wrong, receipt silent, no action needed | `higherDirectImageSheaf` is defined at `ResolutionTransgression.lean:86` and used by two of the four theorems |
| Hygiene: no `sorry`/`axiom`/`maxHeartbeats`/`unsafe`/`native_decide`/`@[simp]`/`private` changes | verified | grep over `git diff 4e15a034 12232351^2` (excluding reports): no hits |
| Build lines, AxiomAudit axiom sets, census ratchet | not checked | needs a build; MERGE.md §Build lines reports the same for the merged state |

Did moving `SphereTwo` lose general material? Read in full: theorem 1 (all abelian sheaves on a space ≃ S² have `R^aΓ = 0` for `a ≥ 3`) is the only candidate for textbook material and it is a 15-line instantiation of the two `Lib` theorems named above plus Mathlib's compactness/paracompactness of the sphere; theorems 2–4 are the manuscript's reformulations (projective-dimension bound for `ℤ_B`, higher-direct-image substitution, the degree 3/4 pair). Nothing general was lost; the general statement (paracompact Hausdorff, `dim ≤ n`) already lives in `Lib`. The `Hopf/Proof` placement is right.

## Not checked

* The build lines, the `Lib.AxiomAudit` axiom-set output and the census ratchet (`lake build` forbidden; MERGE.md reports the merged-state results).
* The raw `_hopf`-suffixed auto-instance names (only the renamed after-dump is on disk; the map's effect is visible, its input is not).
* Whether `lean-agent-ide dump --rename` written "the other way round" really is a silent no-op (receipt claim about the tool; not reproducible without running the dump).
* The `d87ad506` docstring rewrite of the *declaration* was checked; the r7 experiment's exact error text (`AddZero (Sheaf.H F n)` in `FiniteClosedPushforward/Cohomology.lean`) was reproduced only in the `→+` shape, not by rebuilding those two files.

## Tool notes

* A receipt that records a "not done because X" for an instance should include a one-file reproduction (`attribute [-instance] …; #synth …`) so the reviewer can check the cause, not only the symptom; here the symptom reproduced in one elaboration and the stated cause fell in two more.
* `envdiff.json` should keep the pre-rename after-dump names (or the raw name list diff) so the rename map can be checked against its input, not only its effect.
* "Axiom-audited transitively" needs a named probe; if the probe was removed, the receipt should say "unprobed" rather than infer coverage from import closure.
* Docstring file attributions copied from the judgement packet inherit the packet's errors; `grep -rn <name> .lake/packages/mathlib` before writing a path would have caught both.
