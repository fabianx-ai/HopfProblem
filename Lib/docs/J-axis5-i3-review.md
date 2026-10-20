# Lane J — integration-3 Axis-5 typed-ledger review and repairs

**Verdict (initial pass): NO-GO for the typed ledger; J-A's review-3 GO unaffected.**
Reviewer: fresh-context subagent (seat `devin-axis5-j`, integration-3 pass).
Branch `lib/textbook-extraction-muse-i3`, reviewed against HEAD `88e354b` plus the
in-flight `J.md` state. Repair pass applied by Muse immediately after; this file
records the findings and the repairs. A re-confirmation pass is pending and its
result should be appended before this ledger is treated as accepted.

## Findings of the fresh pass

1. **Coordinates.** Essentially every cited source coordinate was stale pre-move
   provenance: `CuspFilling NNNNN`, `Specialization NNNN`, `BoundaryTopology NNNNN`
   and `FiniteCore NNN` references pointed at the monolithic pre-split files.
   Current locations are `Hopf/LCP/CuspFilling.lean` (interface),
   `Hopf/Proof/LCP/CuspFilling.lean` (proofs), `Hopf/LCP/Specialization.lean`,
   `Hopf/Proof/LCP/Specialization.lean`, `Hopf/Proof/FiniteCore.lean`,
   `Hopf/LCP/BoundaryTopology.lean`, and the landed Lib modules
   (`Torus.lean`, `CircleProduct.lean`, `CrossProduct.lean`, `Pontryagin.lean`,
   `MayerVietoris.lean`, `HomotopyInvariance.lean`, `MinorCoordinates.lean`,
   `Degree1.lean`).
2. **Signature-level defects.** (a) Ledger signatures spelled
   `PeriodTorusHigherHomology.crossProductHomology` where the landed Lib provider
   is `SingularHomology.crossProductHomology` — the old spelling resolves only
   through the `Hopf.LibShims` alias, which production packets may not import.
   (b) `coordinatePeriodLoop` was presented with a silent binder rename
   (`n → r`) relative to source.
3. **Stale seam/status claims.** The doc still described S-nat, S-cross and the
   G-J3 coherence suite as unlanded, and `crossProductHomology_natural` /
   `crossProductCycles_natural` / `crossProductHomology_snd` as Hopf-internal.
   All have landed: S-nat outputs in `CircleProduct.lean`, the naturality triad
   and the 110-declaration coherence suite in `CrossProduct.lean` (module).
   Conversely, J-B2a remains gated on the S-path cluster, which is still legacy
   and owner-controlled.
4. **Context gap.** The stated context did not record the production-module
   surface (`namespace Mathoverflow1973`, `open SingularHomology`, `open scoped
   Matrix BigOperators TensorProduct`, `noncomputable section`, the
   `open PeriodTorusHigherHomology` needed for bare `CirclePaths.*` names) or the
   prohibition on `Hopf.LibShims` in production packets.

## Repairs applied (uncommitted, in `Lib/docs/J.md`)

- Every declaration source coordinate remapped to its current file/line; old
  coordinates retained as `was <file>:<line>` provenance annotations.
- Ledger signatures now spell `SingularHomology.crossProductHomology`,
  `AlgebraicTopology.SingularH1`, `AlgebraicTopology.SingularH1.map`,
  `AlgebraicTopology.Hurewicz.loopHomologyClass` and
  `SingularChains.singularComplex` — the public providers — with per-signature
  retarget comments where the source spelling differs.
- `coordinatePeriodLoop` binder rename (`n → r`) annotated in-line.
- Seam text corrected: S-nat landed (`CircleProduct.lean`), S-cross landed
  (`CrossProduct.lean`, module — seam M-C resolved), G-J3 landed
  (`CrossProduct.lean:2065–4342`), J-C2's `crossProductHomology_natural`
  provider landed (:4309). S-path remains unlanded, legacy, and not J-owned;
  J-B2a stays blocked on it alone.
- The 110-declaration G-J3 exclusion manifest and the J-A migration inventory
  are explicitly marked historical (generated from `git show 15bd5f7`).
- J-E's missing-inputs list updated: degree-1 `crossProductHomology_swap` /
  `crossProductHomology_associative` now cited at their landed coordinates
  (CrossProduct.lean:2480 / :4219); the *general-degree* primed variants remain
  absent — J-E stays deferred.
- The stated context records the production-module surface and the
  `Hopf.LibShims` prohibition.

## Re-confirmation pass (fresh context, on the repaired working tree)

The re-confirmation reviewer re-verified all ~150 coordinate/signature claims.
~120 coordinates and all ~60 resolved signature rows checked out verbatim or
modulo the documented retargets. Six defects remained; all were repaired:

1. `J.md:416` falsely called `CirclePaths.*` a CircleProduct.lean provider —
   it is the unlanded Hopf-side S-path cluster (`LCP/CuspFilling.lean:325+`,
   `Proof/LCP/CuspFilling.lean`). Corrected; the signatures now carry a
   provisional-until-S-path caveat.
2. The rank-3 wedge re-run was cited to `Hopf/LCP/BoundaryTopology.lean` and
   described as deleted; it lives in `Hopf/Proof/LCP/BoundaryTopology.lean`
   (`markedWedgeTwo` :2188, `markedWedgeThree` :2197, `singularH2/H3Equiv`
   :16419/:16426) and has not been deleted — J-D's re-route is pending.
3. The 6200–6359 / 6361–6502 block mappings were shifted one block —
   corrected to `LCP/Specialization.lean:405–503` and `:505–648`.
4. The consumer list named `Hopf.FiniteCore` (nonexistent) and attributed
   proof-side content to interface modules — corrected to
   `Hopf.Proof.FiniteCore` / `Hopf.Proof.LCP.*` with per-decl coordinates.
5. The G-J3 suite range was truncated at :4342 — corrected to
   `CrossProduct.lean:2065–4359` (5 occurrences).
6. `quarterIntersectionSection_component` cited ":13430 area" — corrected to
   :13415.

Nits noted: `f034c13` probe-head pins (clarified as historical), Mathlib
line pins (unverifiable locally; names are real), `Proof/CuspFilling`
shorthand (normalized to `Proof/LCP/CuspFilling.lean`).

## Residual limits

- This was a documentation repair, not new mathematics. J-A's review-3 GO stands
  scoped to its 15-node Mathlib-only packet. J-B1 is landed in `Torus.lean` but
  is a candidate pending its own signature census + aggregate consumer test.
- **Re-confirmation of the six repairs: GO** (fresh-context targeted pass — every
  corrected coordinate verified exact; both stale-name and stale-path greps clean).
  The J typed ledger is consistent at HEAD `88e354b` after the two repair rounds.
  This is an Axis-5 ledger-consistency result only: no J-B/J-C/J-D/J-E boundary is
  certified, and J-B2a remains blocked on the unlanded S-path cluster.
