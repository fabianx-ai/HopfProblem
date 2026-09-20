/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Public-API access to `IsLocalDiffeomorphAt` and transparent diffeomorphism variants

Mathlib's `IsLocalDiffeomorphAt`, `Diffeomorph.toPartialDiffeomorph` and
`IsLocalDiffeomorph.diffeomorphOfBijective` are not `@[expose]`d, so module-mode importers
cannot unfold them (no anonymous-constructor, `rcases`, `change` or `rfl` through them).
This file provides what the library needs through the public API only:

* `IsLocalDiffeomorphAt.of_eqOn` : the constructor (a partial diffeomorphism agreeing with `f`
  on its source witnesses `IsLocalDiffeomorphAt f x`), obtained by re-packaging the partial
  diffeomorphism with `toFun := f` and applying `PartialDiffeomorph.isLocalDiffeomorphAt`.
* `IsLocalDiffeomorphAt.exists_partialDiffeomorph` : the destructor, obtained from the
  `localInverse` API.
* `Diffeomorph.toPartialDiffeomorphUniv`, `IsLocalDiffeomorph.diffeomorphOfBijective'` :
  transparent variants (source/target `univ`, resp. `Equiv.ofBijective`) whose function values
  are definitional. They coincide with `Diffeomorph.toPartialDiffeomorph'` and
  `IsLocalDiffeomorph.diffeomorph'` of `Lib.Geometry.Manifold.Transversality.Basic`, which
  cannot be imported by the modules below it in the import graph.
-/

open Set
open scoped ContDiff Manifold

@[expose] public noncomputable section

section API

variable {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
    {f : M → N} {x : M} {n : WithTop ℕ∞}

/-- Constructor for `IsLocalDiffeomorphAt` through the public API: a partial diffeomorphism
`φ` with `x ∈ φ.source` and `f = φ` on `φ.source`. -/
theorem IsLocalDiffeomorphAt.of_eqOn (φ : PartialDiffeomorph I J M N n) (hx : x ∈ φ.source)
    (h : EqOn f φ φ.source) : IsLocalDiffeomorphAt I J n f x := by
  let Φ : PartialDiffeomorph I J M N n :=
    { toFun := f
      invFun := φ.symm
      source := φ.source
      target := φ.target
      map_source' := fun y hy => (h hy).symm ▸ φ.map_source hy
      map_target' := fun y hy => φ.map_target hy
      left_inv' := fun y hy => (congrArg φ.symm (h hy)).trans (φ.left_inv hy)
      right_inv' := fun y hy => (h (φ.map_target hy)).trans (φ.right_inv hy)
      open_source := φ.open_source
      open_target := φ.open_target
      contMDiffOn_toFun := φ.contMDiffOn_toFun.congr h
      contMDiffOn_invFun := φ.contMDiffOn_invFun }
  exact Φ.isLocalDiffeomorphAt I J n hx

/-- Destructor for `IsLocalDiffeomorphAt` through the public API (the `localInverse`). -/
theorem IsLocalDiffeomorphAt.exists_partialDiffeomorph (hf : IsLocalDiffeomorphAt I J n f x) :
    ∃ Φ : PartialDiffeomorph I J M N n, x ∈ Φ.source ∧ EqOn f Φ Φ.source := by
  refine ⟨hf.localInverse.symm, hf.localInverse_mem_target, fun y hy => ?_⟩
  have h1 : hf.localInverse.symm y ∈ hf.localInverse.source := hf.localInverse.map_target hy
  have h2 : hf.localInverse (hf.localInverse.symm y) = y := hf.localInverse.right_inv hy
  calc f y = f (hf.localInverse (hf.localInverse.symm y)) := by rw [h2]
    _ = hf.localInverse.symm y := hf.localInverse_right_inv h1

end API

section Transparent

variable {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Transparent variant of `Diffeomorph.toPartialDiffeomorph`: `source = target = univ` and
`⇑_ = h`, `⇑_.symm = h.symm` are definitional. -/
def Diffeomorph.toPartialDiffeomorphUniv (h : Diffeomorph I J M N ∞) :
    PartialDiffeomorph I J M N ∞ where
  toPartialEquiv :=
    { toFun := h
      invFun := h.symm
      source := Set.univ
      target := Set.univ
      map_source' := fun _ _ => Set.mem_univ _
      map_target' := fun _ _ => Set.mem_univ _
      left_inv' := fun _ _ => h.symm_apply_apply _
      right_inv' := fun _ _ => h.apply_symm_apply _ }
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := fun x _ => h.contMDiff_toFun x
  contMDiffOn_invFun := fun x _ => h.symm.contMDiff_toFun x

/-- Transparent variant of `IsLocalDiffeomorph.diffeomorphOfBijective`, built on
`Equiv.ofBijective`, hence `⇑(hf.diffeomorphOfBijective' hf') = f` is definitional. -/
def IsLocalDiffeomorph.diffeomorphOfBijective' {f : M → N}
    (hf : IsLocalDiffeomorph I J ∞ f) (hf' : Function.Bijective f) :
    Diffeomorph I J M N ∞ where
  toEquiv := Equiv.ofBijective f hf'
  contMDiff_toFun := hf.contMDiff
  contMDiff_invFun := by
    intro y
    have hfgy : f ((Equiv.ofBijective f hf').symm y) = y :=
      (Equiv.ofBijective f hf').right_inv y
    have hmem : y ∈ (hf ((Equiv.ofBijective f hf').symm y)).localInverse.source := by
      have h := (hf ((Equiv.ofBijective f hf').symm y)).localInverse_mem_source
      rwa [hfgy] at h
    have heq :
      EqOn (Equiv.ofBijective f hf').symm
        (hf ((Equiv.ofBijective f hf').symm y)).localInverse
        (hf ((Equiv.ofBijective f hf').symm y)).localInverse.source := by
      intro y' hy'
      apply hf'.1
      trans y'
      · exact (Equiv.ofBijective f hf').right_inv y'
      · exact ((hf ((Equiv.ofBijective f hf').symm y)).localInverse_right_inv hy').symm
    exact ((hf ((Equiv.ofBijective f hf').symm y)).localInverse_contMDiffOn.congr
        heq).contMDiffAt
      ((hf ((Equiv.ofBijective f hf').symm y)).localInverse_open_source.mem_nhds hmem)

end Transparent

end
