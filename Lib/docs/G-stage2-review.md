# Lane G — Stage-2 review (ledger §§1–7 + typed rows)

**SUPERSEDED** — this is a self-review by the lane author; it does not satisfy the
independence condition. The governing review is `G-stage2-astra-review.md` (NO-GO,
findings being repaired in `G.md`).

**Reviewer:** Muse (self-review pass; the scout map is `Lib/docs/G-map.md` (in-tree copy)).
**Head reviewed:** `1cc1784` (post-F0a/F0b landing).
**Scope:** `Lib/docs/G.md` Axis-1 §§1–7 narrative, Axes 2–3 decomposition table, Axis-4
placement, Axis-5 typed ledger — checked against the current sources, not the scout's
older snapshot.

## What was re-verified at head

1. **Every FQN in the ledger resolves.** All 33 G-row declarations are inside
   `namespace Mathoverflow1973` and carry the dotted namespaces the first draft
   omitted: `MorseCancel.*`, `AdaptedWindows.*`, `Smale.*`,
   `Smale.ManifoldMorse.SurgeryWindows.*`. No bare names remain in the table or ledger.
2. **Every coordinate is current.** The scout map's coordinates are for an older
   layout (Recognition 9190–11317, SphereTopology 11803–13393, SingularHomology
   19048–19056). Current positions, all re-grepped at `1cc1784`:
   SingularHomology 14047/14052; SphereTopology 6289/6942/7013/8636/9600/9795/9883/
   9976/10004/10064/10112/10145/10194/14226/14338/14360/14386/14468;
   Recognition 2688/3359/3365/3847/7365/8340/8689/8843/8966/9026/9258/9289/9339/
   9344/9385/9413/9431/9442.
3. **The `SecondCountableTopology` claim is true.** `MorseCancel.
   nonempty_homeomorph_of_homotopySixSphere` (Rec 9431) — the entire inner chain —
   has no `[SecondCountableTopology M]` binder. It appears exactly once, on the
   headline wrapper (Rec 9442), where it is unused by the body
   (`nonempty_homeomorph_of_homotopySixSphere E M hdim hM`). Dropping it in the Lib
   statement loses nothing; the Hopf wrapper keeps its statement verbatim.
4. **Sphere-spelling consolidation is genuinely definitional.**
   `Smale.SixSphere` (SingularHomology 14044) is an `abbrev` for
   `Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1`; `Smale.Hemisphere.Sphere n`
   (SurgeryWindows 562) is `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`,
   so `Hemisphere.Sphere 6` is the same sphere. The `change`/`rw [hdim]` chain in
   `nonempty_homeomorph_of_homotopySixSphere` survives the consolidation.
   `SixSphere` (Recognition 1620), `SphereHomology.UnitSphere 6` (Sphere.lean 61),
   `SixSphereCube.StandardSphere` (Hurewicz 9594) are the same `Metric.sphere` —
   five spellings, one term.
5. **n = 6 pinning is real and must not be "generalized" silently.**
   `exists_outer_index_minimal_ordered_morse_system` (ST 10004) takes no `hdim` but
   hard-codes counts at indices `1`/`5`; `minimal_excellent_morse_extreme_counts_one`,
   the middle-count theorems, and the trade chain all use literal `6`, `5`, `3`, `2`.
   The ledger keeps `n = 6` throughout; the `n ≥ 5` generalization is explicitly
   deferred to lane G′.
6. **Seam inputs are real decls, not prose.** The Reeb endpoint consumes
   `Smale.twoDiskDecompositionOfSublevels` (Rec 9289) /
   `Smale.homeomorphSphereOfSublevelDisks` (Rec 9339) over lane-D1 structures
   (`Smale.TwoDiskDecomposition` ST 8073, `Smale.SublevelDisk` ST 8157) — all exist.
   The middle-matrix inputs (`canonicalMiddleMatrix` Rec 3359, `IsNativeMiddleBasinFamily`,
   `middleSectionClass` Rec 2800) are F10-boundary decls the G rows consume, not
   duplicate.
7. **Module placement is consistent.** G1–G3 → `Morse/MinimalSystem.lean` +
   `Morse/HandleTrade.lean`; G4–G5 → `Morse/MiddleBlocks.lean`; G6 + headline →
   `PoincareConjecture/Smale.lean`. Dependency order in the ledger (G1 < G2 < G3 <
   G4 < G5 < G6) is a chain: G2's minimal-system outputs feed G3's trade, G4's
   middle-matrix surjectivity feeds G5's pivot, G5's count-two feeds G6's Reeb.

## Findings fixed in this pass

- Axes 2–3 table: all coordinates refreshed from the scout snapshot to `1cc1784`;
  every name prefixed with its resolving namespace.
- Axis-5: the bare "ledger is in the map" pointer replaced with the ledger body —
  verbatim signatures where the map gives them, `…`-compressed signatures marked
  compressed with the verbatim source coordinate cited.
- §7 / headline row: stale `Recognition.lean:11314`/`11312` → `9444`/`9442`.

## Verdict

**Ledger GO for extraction planning.** The Axis-5 surface is now exact enough to
probe: every name resolves, every coordinate is current, the two design mutations
(`SecondCountableTopology` drop, sphere consolidation) are verified safe. Lean work
still requires: producer/consumer interface probes + `G-INTERFACE_RECEIPT.md`,
then the module files in dependency order. No `sorry`/`axiom` may land under `Lib/`.
