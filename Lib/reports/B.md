/-! Review-A item 5: this file was split out of the monolithic lane report on
branch `lib/A-surgerywindows-split` (off bda000e). Corrections from review A check 10 are
applied inline (marked **[corrected]**). Provenance receipts for all lanes: `Lib/reports/RECEIPTS.md`.
-/

# Lane B report — fundamental group, van Kampen, simply connected spheres

**Current status (2026-09-13, GLM seat):** the B probe theorem
`simplyConnectedSpace_of_open_cover` is landed in
`Lib/AlgebraicTopology/FundamentalGroup/SimplyConnectedCover.lean` and probed in
`Lib/AxiomAudit.lean` with exact standard axioms; the "[corrected] NOT complete"
line below is history. The van Kampen extraction itself remains open and is not
claimed by this status.

## Landed

- `Lib/AlgebraicTopology/FundamentalGroup/SimplyConnectedCover.lean` (9, da29618)

## Historical draft attempts (subsequent landings recorded below)

- `VanKampen.lean` — 114 BT decls + 51 HW family members. The family's
  three STRUCTURES (LocalPathValue, PathValue, TwoOpenCover) live in
  Hurewicz.lean while their 114 lemmas live in BoundaryTopology.lean; the
  cfg (cfg-vk.json) assembles both. Last build: 26 errors, all cross-family
  (`SimplyConnectedCover.trans_mem` — now landable — and
  `TriangleRegularBaseFundamentalGroup.basedLoop`).
- `TwoSimplyConnectedCover.lean` — 31 decls (19 HW + 12 BT). The closure
  sweeps in project-welded `SpecialPeriods.EllipticAttachingMeridians`
  material via `LoopSquare`; name-based weld rules needed (the text-based
  WELD regex both over-matches names like `adaptedSurgeryWindows` and
  under-matches pure-namespace welds).

## Resume (next session)

1. Land `TwoSimplyConnectedCover.lean`: cfg-tri.json, HW block (19) + BT
   block (12); refine weld to NAME-based prefixes
   (SpecialPeriods./EllipticAttachingMeridians.) plus text-based for the
   recorded web; expect ~2 build rounds.
2. Land `VanKampen.lean`: cfg-vk.json; imports SimplyConnectedCover +
   TwoSimplyConnectedCover once landed.
3. Then EuclideanSphere (14) → `Lib/Topology/InstanceSpheres.lean` per plan,
   and the SH 18734–19048 remainder.

---


---

## Lane B session-4 close

- `LoopSubdivision.lean` (f09e304) + split into the plan's two targets:
  `SimplyConnectedSphere.lean` (14 EuclideanSphere decls — spheres of
  dimension >= 2 simply connected, Prop 1.14).
- `VanKampen.lean` (165, eca3d71) — Hatcher Thm 1.20.
- **[corrected]** Lane B is NOT complete (review A check 10.5): the plan's B probe
  `simplyConnectedSpace_of_open_cover` is still `Hopf/Hurewicz.lean:550`. Remaining: land that
  probe (or record the obstruction), plus per-declaration docstrings. Axiom probes otherwise:
  (`RiemannMapping.exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero` was
  lane H; B's probes are covered by the landed VanKampen family) and
  per-declaration docstrings.

## Current open-cover probe landing (GLM seat run by Devin/Astra)

The historical blocker is obsolete for the current tree: the proof of
`simplyConnectedSpace_of_open_cover` uses only the already-landed
`SimplyConnectedCover` helpers. Its generic statement gives simple
connectedness from an open cover by simply connected sets with a common
basepoint and path-connected pairwise intersections (the van Kampen gluing
principle, Hatcher Theorem 1.20). The verbatim proof moves from
`Hopf/Hurewicz.lean` to `Lib/AlgebraicTopology/FundamentalGroup/SimplyConnectedCover.lean`.


Probe-tail verification: the 54-declaration B/D1/D2 batch is byte-verbatim
from `53c0d47`; source-range hashes are in
`Lib/reports/BD2-probe-tail-provenance.json` and
`Lib/reports/D1-reeb-provenance.json`. The target modules and
`Hopf.Recognition` build with pinned Lean 4.33.0. Lib-only probes and the
permanent axiom audit report exactly `[propext, Classical.choice, Quot.sound]`
for the B open-cover, D1 Reeb, D2 finite-cell and H even-zero square-root
heads. Census **2,287 → 2,234**: 53 counted stock declarations moved, plus
the B root theorem outside the prefix census. The prefix list is unchanged.
The final consolidated consumer-chain check follows the documentation-only
follow-up; it is not claimed rerun in this baseline receipt.
