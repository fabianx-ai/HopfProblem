# Poincaré duality seat: progress

Seat: Claude Fable 5.1 (`claude-fable-5-1`). Branch `lib/poincare`, worktree `/home/goblin/hopf-poincare`.

## State (2026-10-20)

* Plan: `PLAN.md` (`c42bb30d`).
* **M0 done** (`cc1f2561`, `8ad37d02`; receipt `M0.md`): relative singular homology as a quotient
  complex, long exact sequence of a pair, maps of pairs and the five lemma, chain supports,
  excision for open covers, relative Mayer–Vietoris. 1,970 lines. `lake build Lib Lib.AxiomAudit`
  green (9,409 jobs), 3,797 probes within the three standard axioms.
* **M1 done** (`203c0394`, `840d6fd0`, `77e36807`; receipt `M1.md`): convex complements, local
  homology (`≅ ℤ` for `n ≥ 2`), homology balls and chart balls, the local homology covering space,
  orientations, simply connected ⇒ orientable. 1,319 lines. `lake build Lib Lib.AxiomAudit` green
  (9,414 jobs), 3,811 probes within the three standard axioms.
* PLAN §6: comparison with the accepted independent textbook (`2230baec`).
* **M2 done** (`47dbf867`, `13a26fee`, `cf3dd46f`; receipt `M2.md`): Lemma 3.27 (local-to-global)
  for compact subsets of a T₂ manifold modelled on ℝⁿ (n ≥ 2), the fundamental class, H_i = 0
  above n, H_n(M; ℤ) ≅ ℤ for closed connected oriented M, and for closed simply connected M
  (consumer (c) in generic form). 874 lines. `lake build Lib Lib.AxiomAudit` green (9,417 jobs),
  3,822 probes within the three standard axioms.
* **M3 done** (`9a19c1b8`, written by a work agent and replayed by cherry-pick; receipt `M3.md`):
  front/back faces, chain-level cap and cup products, the Leibniz formulas, naturality. 528 lines.
  Homology-level descent not done (carried to M4b).
* **M4a done** (receipt `M4.md`, section M4a): `quasiIso_τ₁` (first-term two-out-of-three),
  duals of split short exact sequences (retractions or sections), the cohomology long exact
  sequence wrappers, relative cohomology `H^q(X, A; ℤ)` with the long exact sequence of the pair,
  **excision in cohomology** for open covers (via the cochain small-simplices theorem and
  `quasiIso_τ₁`), the relative Mayer–Vietoris sequence in cohomology. 1,057 lines.
  `lake build Lib Lib.AxiomAudit` green (9,423 jobs), 3,840 probes within the three standard axioms.
* **M4b done** (`99061bf6`, `f3010739`, `641a45f7`, `df4b6e9b`; receipt `M4.md` §M4b): cocycle
  classes and descent for cochain complexes, the **relative cap product**
  `H^k(X, A) × H_m(X, A) → H_l(X)` with restriction compatibility and the top-degree Kronecker
  formula, the relative fundamental classes `μ_K`, the **duality maps** `D_K` (compatible with
  restriction) and the absolute duality map `φ ↦ [M] ⌢ φ`, relative chains free, **UCT for
  pairs**, and the **Euclidean base case** `D_K` bijective for closed balls in `ℝ^{m+2}`.
  1,050 lines. `lake build Lib Lib.AxiomAudit` green (9,427 jobs), 3,853 probes.
* **M4c begun** (`5db10bc6`): compactly supported cohomology as a direct limit and the limit
  duality map `H^k_c(M) → H_{n−k}(M)` (160 lines). The Mayer–Vietoris/union induction (Hatcher
  3.35/3.36) is **not done**: Poincaré duality for closed oriented manifolds is the hypothesis
  structure `PoincareDuality.IsPoincareDuality` (placeholder **P-1**, `PLACEHOLDERS.md`, with the
  exact missing list).
* **M4d done** (`3f96a02a`; receipt `M4.md` §M4d): unconditional UCT consequences
  (`H^0` torsion-free, `H^{q+1}` torsion-free for projective `H_q`, `H^k(M) = 0` for `k > n`),
  and under P-1: `H^k(M) ≃ H_{n−k}(M)`, `H^n(M) ≅ ℤ`, the **torsion dictionary in dimension 4**
  (consumer (a) in generic form: closed connected oriented 4-manifold, f.g. homology,
  torsion-free `H_1` ⇒ every `H^q(M; ℤ)` torsion-free). 235 lines.
  `lake build Lib Lib.AxiomAudit` green (9,428 jobs), 3,858 probes within the three standard axioms.
* **Consumer (b), the intersection pairing, done in its cup/cap+duality form** (`6387b68b`): the
  cup product on cohomology (`CapProduct/Cup.lean`, 278 lines) and
  `⟨φ ∪ ψ, [M]⟩ = ⟨ψ, [M] ⌢ φ⟩` for closed oriented `M` (`Orientation/IntersectionForm.lean`,
  153 lines). Unimodularity (Prop. 3.38) is open (needs P-1 and double duals of f.g. free modules).
* **Final checks at `6387b68b`**: `lake build Lib Lib.AxiomAudit` → `Build completed successfully
  (9431 jobs)`, 3,865 probes all within `[propext, Classical.choice, Quot.sound]`;
  `lake build Solution S6Shortcuts S6 Challenge` → green (9,490 jobs); `lake build Shared Center`
  → green (8,867 jobs); `python3 scripts/lib_stock_census.py --check` → 123 (ratchet PASS);
  isolation greps empty on `.lean` files; `git diff --check` clean.
* Totals since `bf6688c0`: 27 commits, 39 files, ~9,100 lines added under `Lib/` (code and
  reports). Never pushed, never merged.

## Register

`PLACEHOLDERS.md`: one entry, **P-1** `PoincareDuality.IsPoincareDuality hn μ` (Poincaré duality for
closed oriented manifolds; the Mayer–Vietoris induction of Hatcher 3.35/3.36).
