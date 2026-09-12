# Next steps — GLM (after the reviews of 2026-09-08 and 2026-09-12)

Branch: `lib/textbook-extraction` at 856e4762 (your lane A plus Kimi's C, E2, F, G, J are merged
there; builds green). Start every new lane from this head. Reviews: `Lib/reviews/A.md` (your
branch) and `Lib/reviews/INTEGRATION.md` (§ "For GLM").

## Owner decisions you are waiting on (do not guess; ask in the report if still open)

- **SurgeryWindows.** `Lib/Geometry/Manifold/Morse/SurgeryWindows.lean` is 44 % lane E2, 31 % E1,
  8 % F by source position and only 28 declarations are D2. Owner picks: (a) split along the
  plan's E1/E2/F targets as a pure move of moves, or (b) record the composition in the docstring
  and hand the file to Kimi's E2 as its starting point. Until decided, do not touch the file
  beyond its docstring.

## In this order, one branch per item, each branch `lib/A-fix-<n>-<slug>` off 856e4762

1. **Register the ten unrooted modules in `Lib.lean`** (review A, item 2). One commit, builds
   `Lib`, ratchet unchanged.
2. **Provenance receipts** (review A, item 1): a table `721fc82 file:range → SHA-256 of that exact
   range → target file` for the 27 baseline commits without one and the eleven lane-A files
   inside `44c11efc`, ranges cut at declaration boundaries so the hashes reproduce. Goes into the
   per-lane reports (item 5). No history rewrite.
3. **FREE rule inside `Lib/`** (review A, item 3): rename `SpecialPeriods.exists_analytic_unit_root`
   with a shim; replace the 20 stale pre-rename names in docstrings listed under check 6; drop
   the `Hopf.Recognition` mention in `Lib/AxiomAudit.lean`.
4. **The 78 `dupNamespace` warnings** (review A, item 4): one rename commit, no proof-term
   change, shim updated, `lake build Lib` with zero warnings as the receipt.
5. **Split the report** into `Lib/reports/{A,D1,D2,H,I,B,E1}.md` with the corrections in review A
   check 10, items 1–9. Lane B is not complete while `simplyConnectedSpace_of_open_cover` is in
   `Hopf/Hurewicz.lean`; say so and finish it or record the obstruction.
6. **Lane I, Wang sequence** — now unblocked: import
   `Lib.AlgebraicTopology.SingularHomology.CrossProduct` from
   `Hopf/LCP/{CuspFilling,IntegralHomology}.lean` and land `Lib/Topology/MappingTorus/Wang.lean`.
   The 42 coherence declarations in `Hopf/LCP/Specialization.lean` are Kimi's J item; leave them.
7. **Lane E1**: first commit your `Cubic`/`TimeChange`/`LevelCylinder` drafts to the fork (a
   `drafts/` directory under `Lib/reports/` is fine) so they exist off your machine; then resume
   from the three probe theorems still in `Hopf/` (`MorseCancel.cancel_of_transverse_level_isotopy`,
   `Degree.MorseRearrangement.exists_morse_rearrangement_of_no_connection`,
   `MorseCancel.exists_excellent_indexed_morse_birth`), after the SurgeryWindows decision.
8. **Docstrings**, ongoing and largest: 24 files without a module docstring, 62 without section
   headers, 4,245 public declarations without one. Model: `Lib/AlgebraicTopology/Hurewicz/Degree1.lean`
   (module docstring) and `Lib/AlgebraicTopology/SingularHomology/CrossProduct.lean` (per
   declaration). Do this per file, one commit per file, "No proof term changed."
9. **Rename commits** for the transitional namespaces (`Smale.*`, `NoExotic.*`, `Degree.*`,
   `MorseCancel.*`, `SingularMayerVietoris.*`, `SphereHomology.*`, `RiemannMapping.*`,
   `HolomorphicCousin.*`, `MappingTorus*`, `FundamentalGroupVanKampen.*`, `Mathoverflow1973`),
   naming the Mathlib twin file in each commit message. A lane is done only when its rename has
   landed.

## Rules that the review found broken; they hold from now on

- One branch per lane, one report per lane, commit messages that name commits that exist.
- Every baseline commit carries the reproducible SHA-256 of the exact range moved.
- The shared Lean environment at the path the owner gave you is at the pinned Mathlib and
  toolchain; do not fetch a cache into it and do not report it stale.
- Nothing is "COMPLETE" while its probe theorem is still under `Hopf/`.
