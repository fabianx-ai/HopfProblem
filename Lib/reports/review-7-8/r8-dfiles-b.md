# Review of Lib/reports/round-8/dfiles-b/RECEIPT.md

**Verdict: ACCEPT WITH FINDINGS** — every move, rename and extraction is statement-preserving and
fully reconciled against envdiff, but one of the three deletions (`fibre_constant_of_ker_le`) has
no *named* surviving twin, and the receipt misplaces the Mathlib file of the other two.

Reviewer: r8-dfiles-b (fresh, no prior context). Branch `r8/dfiles-b`, base `4e15a034`, merge
`1302a5e8`, compared against head `39f1d12b`. All 12 commits and the whole branch diff were read;
the ~60 declarations touched were checked exhaustively (not sampled).

## Findings

1. **[incomplete] `fibre_constant_of_ker_le` was deleted without a named twin.**
   Deleted (`git show 4e15a034:Lib/Algebra/Group/SurjectiveDescent.lean`, l.35):
   ```
   theorem fibre_constant_of_ker_le {A B C : Type*} [Group A] [Group B] [Group C]
       (f : A →* B) (g : A →* C) (hker : f.ker ≤ g.ker) : ∀ a b, f a = f b → g a = g b
   ```
   The receipt's "twin" is `Mathlib's { g // f.ker ≤ g.ker } subtype packaging` — a type, not a
   declaration, and it does not state this implication. I searched
   `/home/goblin/hopf-lib-integration/.lake/packages/mathlib` (`ker_le_ker`, `ker_le`, `eq_of_ker_le`,
   `le_ker_iff` in `Algebra/Group/Subgroup/*`, `GroupTheory/*`): Mathlib has no lemma of this
   shape. `MonoidHom.liftOfRightInverse_comp_apply` is not a twin either (it needs a right inverse
   of `f`; the deleted lemma has no surjectivity hypothesis). The content is a four-line
   consequence of `MonoidHom.mem_ker` + `eq_of_mul_inv_eq_one` (I re-proved it in my probe file,
   `r8-dfiles-b/Probe.lean`, elaborates green), so nothing mathematical is lost and the lemma had
   no consumer outside `AxiomAudit` — but the protocol asks for a named twin or an explicit
   "deleted, no twin, because …" entry. The receipt's lost-names table should say the latter
   (and so should `Lib/reports/round-8/MERGE.md`, which the assignment says names no twin).

2. **[wrong receipt] Wrong Mathlib file for `MonoidHom.liftOfSurjective`.** Receipt and commit
   `fff26c16` both say `Mathlib/Algebra/Group/Subgroup/Ker.lean`. The declaration is in
   `Mathlib/Algebra/Group/Subgroup/Basic.lean` l.930 (`grep -n liftOfSurjective
   Mathlib/Algebra/Group/Subgroup/Ker.lean` is empty; the packet had it right at "Basic.lean l.932").
   The twins themselves are correct: `MonoidHom.liftOfSurjective : (f : G₁ →* G₂) →
   Function.Surjective f → { g // f.ker ≤ g.ker } ≃ (G₂ →* G₃)` (an `abbrev` for
   `liftOfRightInverse` at `Function.surjInv`) and `liftOfRightInverse_comp : (f.liftOfRightInverse
   f_inv hf g).comp f = g` — same or stronger than the deleted `descendHomOfSurjective` /
   `descendHomOfSurjective_comp` (fibre-constancy ⇒ `f.ker ≤ g.ker` by `a, 1`; my probe builds
   `descendHomOfSurjective` as `f.liftOfSurjective hf ⟨g, _⟩`). The receipt's claim that
   `MonoidHom.liftOfSurjective_comp` does not exist in v4.33.0 is true (`#check` → unknown constant;
   only `RingHom.liftOfSurjective_comp` exists).

3. **[nit] Packet suggestions silently not taken.** The packet asked, for
   `Hurewicz/SphereGenerator.lean`, to "state `exists_sphereMap_of_homologyEquiv` for general
   `n ≥ 2` next to `HopfDegree.sphere_homotopicRel_of_topClass_eq`" before moving; for
   `FiniteStarCharacter` and `SignedResidual` to inline at the call site. None was done; the
   receipt neither does them nor lists them under "Left for a later round". The moves are
   statement-preserving, so this is a reporting gap, not unsoundness. Note also that
   `ResidualRelations`, `FiniteStarCharacter` and `LatticeImageCollapse` have **no consumer at
   all** (verified at base: only `Lib.lean`/`AxiomAudit.lean` mention them) and are kept alive
   solely by three new imports in `Hopf/Proof/Final.lean` — the receipt says so, but "dead code
   parked under Hopf/Proof" is the honest description.

4. **[nit] A stock `Hopf/` file now imports `Hopf.Proof`.** `Hopf/Recognition.lean` (stock, not
   `Hopf/Proof`) gained `import Hopf.Proof.AlgebraicTopology.Hurewicz.DegreeSix`; at base it had
   zero `Hopf.Proof` imports (`git show 4e15a034:Hopf/Recognition.lean | grep -c "^import
   Hopf.Proof"` → 0). Not forbidden by any rule in the brief and the census ratchet only counts
   declarations, but the receipt does not mention that the stock/proof import direction changed.
   Similarly the unused `import Lib.GroupTheory.PresentedGroup.CentralTwist` lines in stock
   `Hopf/LCP/{BoundaryTopology,IntegralHomology}.lean` were dropped (correct — `TwistGroup` is used
   only in `Hopf/Proof/LCP/BoundaryTopology.lean`) but are not listed in the receipt.

5. **[nit] Unlisted edits in `Lib/AxiomAudit.lean` and the moved files.** (a) A new section header
   `/-! ## Lib.Algebra.Group.DeterminingFamily -/` was inserted (the `DeterminingFamily` probes had
   been sitting under the removed `LatticeImageCollapse` header) — harmless, unmentioned.
   (b) The seven moved files drop the `Copyright (c) 2026 Fabian Franz` / `Authors` header lines
   for the `Hopf/Proof` SPDX style, but omit the `/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/`
   first line every other `Hopf/Proof` file carries. (c) `CentralTwist.lean` also lost its unused
   `open Set Function Filter Manifold Topology` line. All cosmetic.

6. **[citation] Weibel §5.2 for `LowerDifferentials.lean` — plausible, not certain.** Weibel §5.2
   ("Terminology") defines bounded spectral sequences, convergence and edge maps, and treats the
   two-column collapse; I do not recall a three-column statement there. The reference is to the
   section, not a numbered result, so it is not wrong, only loose. The Hatcher §2.2 citation on
   `SpherePointTransport.lean` (degree of sphere maps, reflection has degree −1) is correct.

No `[unsound]` finding: no statement changed, no hypothesis added, no `sorry`/`axiom`/
`maxHeartbeats`/`native_decide`/`unsafe`/`@[simp]` change/`private` removal/`noncomputable`
addition in the branch diff (only `@[expose] public noncomputable section` → `noncomputable
section` in the two moved non-module files). `git grep "import Hopf" 39f1d12b -- 'Lib/**/*.lean'`
is empty (all hits are in `Lib/docs`/`Lib/reports` prose).

## Claims checked

| claim | status | how |
| --- | --- | --- |
| 12 commits on the branch, one per file except `DegreeSix`+`SphereGenerator` | verified | `git log 4e15a034..1302a5e8^2`; base `SphereGenerator.lean` l.6 imports `DegreeSix`, so a split would have left a Lib file importing `Hopf.*` — reason holds |
| Commit trailers present on every commit | verified | each of 12 commits has `Co-Authored-By` + `Claude-Session` |
| `SurjectiveDescent.lean` deleted; only consumer `Lib/AxiomAudit.lean` | verified | `git grep` at base: file, `Lib.lean`, `AxiomAudit` only; commit `fff26c16` removes exactly those |
| `descendHomOfSurjective` → `MonoidHom.liftOfSurjective`, `_comp` → `liftOfRightInverse_comp` | verified (statements) / refuted (file path) | Mathlib `Subgroup/Basic.lean` l.911–945; probe `#check`s; see finding 2 |
| `fibre_constant_of_ker_le` twin | refuted as a *named* twin | finding 1 |
| `MonoidHom.liftOfSurjective_comp` absent in v4.33.0 | verified | probe: unknown constant; grep shows only `RingHom.`/`Ideal` versions |
| Seven files moved to `Hopf/Proof/...` with content unchanged apart from header/imports/docstring | verified | `git diff 4e15a034:Lib/<p> 39f1d12b:Hopf/Proof/<p>` for all seven: only header, `module`/`public` keywords, one import retarget (`SphereGenerator`), the unused `SplitExtension` import and one `open` line dropped, module docstrings rewritten; all seven identical between branch tip and head |
| Each moved file is project-specific | verified (judgement) | read all seven at base: `A1`/`A2`/`![1,2,-4,0]` matrices; exponents 3,4 = orders of `T₁`,`T₂`; `TwistGroup` presentation; degree 6 hard-coded (`SixthHurewicz.*`, `hpi … k < 6`); `3u = k, -4v = k`; `exists_stageCharacter` is `Finset.induction_on` with a dependent predicate (Mathlib already has the general form). Nothing a general library would keep beyond what Mathlib has |
| No `Lib` import of any moved/deleted module remains | verified | `git grep -E "Lib\.(…moved modules…)" 39f1d12b -- '*.lean'` empty; `import Hopf` in `Lib/*.lean` empty |
| `LatticeImageCollapse` duplicates `LatticeCuspNormalClosure.*`; `image_firstBasis_eq` has no counterpart | verified | `Hopf/Proof/LCP/BoundaryTopology.lean` l.20644–20726 has `image_eq_one_of_gamma_eq_zero`, `image_eq_zpow_gamma`, `image_epsilon_prime_eq`, `image_epsilon_commute_{first,second}`; no `firstBasis` |
| `MeshScale` folded into its only consumer, statement unchanged | verified | commit `b67b67df`: base consumers = `MeshScale`, `AxiomAudit`, `CubeBoundaryThreeLebesgue`; statement textually identical except `√2` → `Real.sqrt 2` (probe prints `h * √2 < lambda`) |
| `LowerTransfer` island: 5 generic `[CommRing R]` declarations, consumed by a Lib file, renamed with statements unchanged | verified | commit `67f49883` diff: bodies identical line for line; `ThreeColumnSpectralSequence/LowerTransfer.lean` consumes it |
| Rename map: 8 entries, both files, one per direction, consistent | verified | `rename.txt` is `rename-old-to-new.txt` with columns swapped; old names absent from all `.lean` at head; every new name present |
| `LocalDegreeNeighborhoods` 65 → 58 declarations; 5 to `LinearSphereAction`, 2 to `Reeb` | verified | decl-keyword count at base/tip: 65/58; commit `513197b9` removed exactly those 7, bodies identical at destination; `Reeb.lean` gains the `HomotopyInvariance` import |
| `OnePointCover` 48 → 35; 13 `SpherePoint.*` to new `SpherePointTransport.lean` importing only `Mathlib` + `LinearSphereAction` | verified | count 48/35; comment-stripped removed lines ⊂ new file (0 added-only lines); imports l.6–7 |
| `SublevelDisk` is declared in `Morse/Reeb.lean` (not `SublevelSets`) | verified | `Reeb.lean` docstring "Main definitions: `SublevelDisk`" |
| Consumers that block moving the two files: `SurgeryCollapse` (+`MiddleBlocks`, `SurgeryHomology`) | partly | at base `SurgeryCollapse.lean` consumes every listed name; `MiddleBlocks.lean` and `CutTransport.lean` consume `singlePoint_cover`/`instLocal*`; no hit for these names in `SurgeryHomology.lean` |
| `SplitExtension` kept (round 7) and `Contragredient` already deleted at base | verified | `Lib/reports/round-7/names/RECEIPT.md` l.68; commit `86377b36` deleted `Contragredient.lean`; `SplitExtension.lean` exists at head |
| envdiff: lost 8 = 3 source + 5 aux, added 3 aux, no type change; moves as listed | verified | `envdiff.json`: lost = 3 `SurjectiveDescent` names + `descendHomOfSurjective._proof_{1,2}` + `Int.signed_residual_coordinate_zero._proof_1_1` + `LowerTransferCondition.{_proof_1,eq_1}`; added = the 3 renamed aux constants; 12 move rows sum to 86 = 14+1+5+1+21+2+5+2+13+1+1+20 |
| `Lib.lean`: 10 imports removed, 2 added (`SpherePointTransport`, `LowerDifferentials`) | verified | `git diff 4e15a034 1302a5e8^2 -- Lib.lean` |
| `Hopf/Proof/Final.lean` pulls in the three consumer-less modules | verified | branch diff adds the three imports |
| Docstrings added on the 5 + 2 + 13 extracted declarations match their statements | verified | read `LinearSphereAction.lean` l.518–584, `Reeb.lean` l.725–737, `SpherePointTransport.lean` l.44–187 against the printed types |
| Build green, axiom census, `lib_stock_census.py` 123 ≤ 1648 | not checked | see below |

## Not checked

* The `lake build` result, the 1712/112/10/12 axiom-line counts and the census ratchet number:
  would need a build; I only elaborated one probe file against the built head (all `#check`s
  resolve, `#print axioms` on two extracted theorems gives `[propext, Classical.choice,
  Quot.sound]`).
* That the `Hopf/Proof` copies still compile in their new location with `import Mathlib` and the
  retained `set_option maxSynthPendingDepth 3`/`warningAsError` — head is built, so implicitly yes.
* Whether later branches (dfiles-a touched `LinearSphereAction.lean` +55 lines,
  `OnePointCover.lean`, `LocalDegreeNeighborhoods.lean` after this merge) preserved this branch's
  edits; I diffed only this branch's tip against head for the files it created/moved (identical).
* Universe lifts / binder widenings: none claimed and none seen in the diff.

## Tool notes

* The receipt's lost-names table should be forced to name a *declaration* per lost source name
  (or an explicit "no twin, reason"); a free-text cell like "Mathlib's `{ g // … }` subtype
  packaging" passed the envdiff reconciliation while naming nothing checkable.
* Mathlib twin citations should carry `file:line` produced by `grep`, not from memory — both the
  receipt and the commit message copied a wrong file name that the packet had right.
* `envdiff` "moves" rows are 1-to-1 counts only; a per-declaration old→new list (even for moves)
  would have let me skip the manual comment-stripped body comparison of `OnePointCover` vs
  `SpherePointTransport`.
