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
* M3 next: cap and cup products at the chain level (`SingularCochains/CapProduct/`).

## Register

`PLACEHOLDERS.md`: empty.
