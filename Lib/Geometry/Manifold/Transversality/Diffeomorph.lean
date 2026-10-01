/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.Existence
public import Lib.Geometry.Manifold.RegularLevel
public import Lib.Geometry.Manifold.WhitneyEmbedding
public import Lib.Geometry.Manifold.Collar
public import Lib.Geometry.Manifold.Morse.SurgeryWindows
public import Lib.Geometry.Manifold.Morse.CubicFlow
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
/-!
# Diffeomorphisms with definitional underlying maps

Two constructions of Mathlib re-done so that their underlying functions unfold definitionally for
importers under the module system: a global diffeomorphism viewed as a partial diffeomorphism with
source and target `univ`, and the diffeomorphism defined by a bijective local diffeomorphism
(a bijective local diffeomorphism is a diffeomorphism, cf. Lee, *Introduction to Smooth
Manifolds*, Ch. 4).

## Main definitions

* `Diffeomorph.toPartialDiffeomorph'` : a diffeomorphism as a partial diffeomorphism.
* `IsLocalDiffeomorph.diffeomorph'` : a bijective local diffeomorphism as a diffeomorphism, with
  `⇑(hf.diffeomorph' hf') = f` definitionally.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff Matrix NNReal

@[expose] public noncomputable section

/-- Transparent variant of `Diffeomorph.toPartialDiffeomorph`: Mathlib's version is not
`@[expose]`d, so under the module system its fields do not unfold for importers. This
version keeps `source = target = univ` and `⇑_ = h`/`⇑_.symm = h.symm` definitional. -/
def Diffeomorph.toPartialDiffeomorph' {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [TopologicalSpace N]
    [ChartedSpace H' N] [IsManifold J ∞ N] (h : Diffeomorph I J M N ∞) :
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

/-- Transparent variant of `IsLocalDiffeomorph.diffeomorphOfBijective`: Mathlib's version is
not `@[expose]`d, so its function values do not unfold for module-mode importers. Built on
`Equiv.ofBijective`, hence `⇑(hf.diffeomorph' hf') = f` is definitional. The inverse is
smooth because near each `y` it agrees with the local inverse at `g y`. -/
def IsLocalDiffeomorph.diffeomorph' {E F H H' M N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] {f : M → N}
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
