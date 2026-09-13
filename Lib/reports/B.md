/-! Review-A item 5: this file was split out of the monolithic lane report on
branch `lib/A-surgerywindows-split` (off bda000e). Corrections from review A check 10 are
applied inline (marked **[corrected]**). Provenance receipts for all lanes: `Lib/reports/RECEIPTS.md`.
-/

# Lane B report — fundamental group, van Kampen, simply connected spheres

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

