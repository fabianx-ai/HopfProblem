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
* M2 next: `Orientation/LocalToGlobal.lean` (the property, the Mayer–Vietoris step, the agreement
  lemma, chart-convex sets), `Orientation/FundamentalClass.lean` (support argument, chart cover,
  Theorem 3.26).

## Register

`PLACEHOLDERS.md`: empty.
