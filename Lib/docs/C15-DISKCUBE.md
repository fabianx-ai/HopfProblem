# C15 — `DiskCube` extraction to `Lib`

Typed ledger for moving the `Mathoverflow1973.DiskCube` block out of
`Hopf/Hurewicz.lean` into `Lib/Topology/Homeomorph/DiskCube.lean`. Integrated base
`f9a24ba`, branch `lib/C-14-integrated-receipt`.

## Provenance

- Source: `Hopf/Hurewicz.lean` lines 100–185 at `f9a24ba` — twelve declarations,
  `DiskCube.target` through `DiskCube.symm_boundary_iff`. The block contains no
  comments.
- Source byte checksum: SHA-256 of the exact UTF-8 newline-preserving slice
  `lines[99:185]` (1-based lines 100–185) is
  `4a7c7223b148a00a874d69a898fcf4f511727deb18af128036fd82de0e1f20f2`.
  The source bytes are preserved at `/home/kimi/s6-notes/C15-diskcube-source-block.txt`.
- Transfer rule: the block is pasted unchanged except the single namespace
  normalization `HigherHurewicz.` → `Hurewicz.` (the shim spelling used inside
  `Hopf`); no proof text is altered. Per-declaration docstrings are added as
  requested documentation and do not touch proof terms.
- The `Mathoverflow1973.DiskCube` namespace is retained for the GLM-owned global
  wrapper removal; `Hopf/Hurewicz.lean` imports the new module so all public names
  and statements are unchanged.
- No `0 < n` hypothesis is added: the boundary correspondence holds at `n = 0`.

## Mathematics

For a finite-dimensional real normed space `V` and a continuous linear equivalence
`L : V ≃L[ℝ] (Fin n → ℝ)`, the closed unit ball `DiskCylinder.Disk (E := V)` is
homeomorphic to the unit cube `Fin n → unitInterval`, and the norm-one boundary
corresponds to `Cube.boundary (Fin n)`. The pulled-back cube `target L =
L ⁻¹' realCubeSet n` is convex, compact, and has nonempty interior;
Mathlib's `exists_homeomorph_image_eq` (from
`Mathlib/Analysis/Convex/GaugeRescale.lean`, the ambient-homeomorphism lemma for
bounded convex sets with nonempty interior, preserving image, closure, and frontier)
applied to the closed unit ball and `target L` gives an ambient homeomorphism
matching both the balls and their frontiers. Composing `ambient L`, `L`, and
`realCubeHomeomorph n` and restricting to the ball gives the homeomorphism; the
boundary characterization follows from `frontier_closedBall` and
`mem_sphere_zero_iff_norm`.

## Nodes (exact source signatures)

```lean
def DiskCube.target {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {n : ℕ}
    (L : V ≃L[ℝ] (Fin n → ℝ)) : Set V

theorem DiskCube.target_compact {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) : IsCompact (target L)

theorem DiskCube.target_convex {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) : Convex ℝ (target L)

theorem DiskCube.target_interior_nonempty {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    (interior (target L)).Nonempty

theorem DiskCube.exists_ambient {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    ∃ e : V ≃ₜ V,
      e '' Metric.closedBall (0 : V) 1 = target L ∧
        e '' frontier (Metric.closedBall (0 : V) 1) = frontier (target L)

def DiskCube.ambient {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) : V ≃ₜ V

theorem DiskCube.ambient_image {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    ambient L '' Metric.closedBall (0 : V) 1 = target L

theorem DiskCube.ambient_frontier {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    ambient L '' frontier (Metric.closedBall (0 : V) 1) = frontier (target L)

theorem DiskCube.ambient_mem_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) (v : V) :
    v ∈ Metric.closedBall (0 : V) 1 ↔ L (ambient L v) ∈ Hurewicz.realCubeSet n

def DiskCube.homeomorph {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ)) :
    DiskCylinder.Disk (E := V) ≃ₜ (Fin n → unitInterval)

theorem DiskCube.boundary_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ))
    (z : DiskCylinder.Disk (E := V)) :
    homeomorph L z ∈ Cube.boundary (Fin n) ↔ ‖(z : V)‖ = 1

theorem DiskCube.symm_boundary_iff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {n : ℕ} (L : V ≃L[ℝ] (Fin n → ℝ))
    (z : Fin n → unitInterval) :
    ‖((homeomorph L).symm z : V)‖ = 1 ↔ z ∈ Cube.boundary (Fin n)
```

(Statements above shown with the post-move `Hurewicz.` normalization already applied;
the source block spells the same names `HigherHurewicz.` via the shim.)

## Interface receipt

Honest labelling: the pre-move probes record the **existing** interface implemented
in `Hopf` — they are the baseline the move must preserve, not a frozen
pre-implementation challenge.

- Pre-move provider `C15_DiskCubeInterfaceCheck.lean` (`import Hopf.Hurewicz`,
  twelve `abbrev` aliases): `lake env lean -o` exit 0; log
  `~/s6-notes/C15-interface-pre-provider.log`, source
  `~/s6-notes/C15-interface-pre-provider.lean`.
- Pre-move consumer `C15_DiskCubeConsumerCheck.lean` (imports the provider, `#check`s
  all aliases, arbitrary-`V` `homeomorph`/`boundary_iff` examples, `n = 0` example):
  exit 0; log `~/s6-notes/C15-interface-pre-consumer.log`, source
  `~/s6-notes/C15-interface-pre-consumer.lean`.
- Post-move provider `lake env lean -o C15_DiskCubeInterfaceCheck.olean
  C15_DiskCubeInterfaceCheck.lean` (same body, `import
  Lib.Topology.Homeomorph.DiskCube`) — exit 0, epoch 1789269184→1789269187; log
  `~/s6-notes/C15-interface-post-provider.log`, source
  `~/s6-notes/C15-interface-post-provider.lean`.
- Post-move consumer `LEAN_PATH=.:$LEAN_PATH lake env lean
  C15_DiskCubeConsumerCheck.lean` — exit 0, epoch 1789269196→1789269200; log
  `~/s6-notes/C15-interface-post-consumer.log`, source
  `~/s6-notes/C15-interface-post-consumer.lean`.
- Builds: `lake build Lib.Topology.Homeomorph.DiskCube` exit 0
  (`~/s6-notes/C15-diskcube-build.log`); `lake build Hopf.Hurewicz` exit 0
  (`~/s6-notes/C15-hurewicz-build.log`). Census `--check` PASS 2651 ≤ 2663, then
  `--update` lowered the baseline to 2651 (`~/s6-notes/C15-census.log`).
