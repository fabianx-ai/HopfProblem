/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.MayerVietoris
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.Sphere
import Lib.AlgebraicTopology.SingularHomology.SphereHomology
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Flow.HeightTranslating
import Lib.Geometry.Manifold.Immersion.Relative
import Lib.Geometry.Manifold.Transversality.Basic
import Lib.Geometry.Manifold.Morse.HandleAttachment
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.Cancellation
import Lib.Geometry.Manifold.Morse.Rearrangement
import Lib.Geometry.Manifold.Morse.Connection
import Lib.Geometry.Manifold.Morse.CellStructure
import Lib.LinearAlgebra.Matrix.TransvectionReduction

/-!
# Sublevel sets of a real function: inclusions, equal cuts and homology

The general part of the former `Lib.Geometry.Manifold.Morse.CutTransport`, kept
after the round-7 audit returned that module's index-2/3 bookkeeping to
`Hopf/Proof/` (`Hopf.Proof.Geometry.Manifold.Morse.CutTransport`).

For a continuous `f : M → ℝ` and `a ≤ b`, `MorseCancellation.sublevelMap` is the
inclusion `{f ≤ a} → {f ≤ b}` and `levelSublevelMap` the inclusion of the level
set `{f = a}`; `sublevelMap_trans` and `sublevelHomologyMap_comp` say these are
functorial, and `middleSectionClass` is the degree-`2` singular homology class of
a `2`-sphere section of a level set, read in the sublevel set.

Two functions with the same sublevel set at `a` ("equal cuts") give a homeomorphism
`equalCutSublevelHomeomorph` of sublevel sets, hence an isomorphism
`equalCutHomologyEquiv` on `H₂`; `equalCutSection` transports sections,
`equalCutSection_class` says the isomorphism carries one section class to the
other, and `equalCutSection_trans`, `equalCutHomologyEquiv_refl`,
`equalCutHomologyEquiv_trans` are the groupoid laws.

`SupportedDiffeomorph.IsotopicToIdentity.homotopic` and `comp_homotopic` record
that a diffeomorphism isotopic to the identity is homotopic to it (so it acts
trivially on homotopy and homology), and `SupportedDiffeomorph.IsotopicToIdentity.conj` that this is
stable under conjugation by a diffeomorphism.

`Submodule.span_range_fin_succ` (the span of the first `k + 1` members of a family is the span
of the first `k` joined with the last) and
`Set.ncard_range_comp_inter_range_comp_of_injective` (`Set.ncard` of an intersection of two
ranges is invariant under an injection) are general algebra/set lemmas used here;
they are co-located rather than filed under `Lib/LinearAlgebra` and `Lib/Data/Set`
only to keep this change a move.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §3, Thm. 3.4.
* [Allen Hatcher, *Algebraic topology*][hatcher02], §2.2.

## Tags

sublevel set, level set, singular homology, isotopy, Morse theory
-/
open Set Function Filter Manifold Topology

open scoped ContDiff

noncomputable section

def MorseCancellation.levelSublevelMap {M : Type} [TopologicalSpace M] (f : M → ℝ) {a b : ℝ}
    (hab : a ≤ b) : C({ y : M // f y = a }, { y : M // f y ≤ b }) :=
  ⟨fun y => ⟨y.val, y.property.le.trans hab⟩, continuous_subtype_val.subtype_mk _⟩


def MorseCancellation.sublevelMap {M : Type} [TopologicalSpace M] (f : M → ℝ) {a b : ℝ} (hab : a ≤ b) :
    C({ y : M // f y ≤ a }, { y : M // f y ≤ b }) :=
  ⟨fun y => ⟨y.val, y.property.trans hab⟩, continuous_subtype_val.subtype_mk _⟩

def MorseCancellation.middleSectionClass {M : Type} [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (γ : C((Hemisphere.Sphere 2), { y : M // f y = a })) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 :=
  SingularMayerVietoris.singularHomologyMap ((levelSublevelMap f le_rfl).comp γ) 2
    (SphereHomology.unitSphereTopClass 1)

theorem MorseCancellation.sublevelMap_trans {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    (f : M → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (sublevelMap f hbc).comp (sublevelMap f hab) = sublevelMap f (hab.trans hbc) :=
  rfl

theorem MorseCancellation.sublevelHomologyMap_comp {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (f : M → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (k : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (sublevelMap f hbc) k).comp
        (SingularMayerVietoris.singularHomologyMap (sublevelMap f hab) k) =
      SingularMayerVietoris.singularHomologyMap (sublevelMap f (hab.trans hbc)) k := by
  rw [← SingularHomology.singularHomologyMap_comp, sublevelMap_trans]


theorem Submodule.span_range_fin_succ {A : Type} [AddCommGroup A] [Module ℤ A] {n k : ℕ}
    (v : Fin n → A) (hk : k < n) :
    Submodule.span ℤ (Set.range (fun j : Fin k => v ⟨j.val, j.isLt.trans hk⟩)) ⊔
        Submodule.span ℤ {v ⟨k, hk⟩} =
      Submodule.span ℤ (Set.range (fun j : Fin (k + 1) => v ⟨j.val, by omega⟩)) := by
  have heq :
    (fun j : Fin (k + 1) => v ⟨j.val, by omega⟩) =
      Fin.snoc (fun j : Fin k => v ⟨j.val, j.isLt.trans hk⟩) (v ⟨k, hk⟩) := by
    funext j
    cases j using Fin.lastCases <;> simp
  rw [heq, Fin.range_snoc, Submodule.span_insert, sup_comm]


def MorseCancellation.equalCutSection {M : Type} [TopologicalSpace M] {f g : M → ℝ} {a : ℝ}
    (hlevel : ∀ y, g y = a ↔ f y = a) (γ : C((Hemisphere.Sphere 2), { y : M // f y = a })) :
    C((Hemisphere.Sphere 2), { y : M // g y = a }) :=
  ⟨fun x => ⟨(γ x).val, (hlevel _).mpr (γ x).property⟩,
    (continuous_subtype_val.comp γ.continuous).subtype_mk _⟩

def MorseCancellation.equalCutSublevelHomeomorph {M : Type} [TopologicalSpace M] {f g : M → ℝ} {a : ℝ}
    (hsub : ∀ y, g y ≤ a ↔ f y ≤ a) : { y : M // f y ≤ a } ≃ₜ { y : M // g y ≤ a }
    where
  toFun y := ⟨y.val, (hsub y).mpr y.property⟩
  invFun y := ⟨y.val, (hsub y).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

def MorseCancellation.equalCutHomologyEquiv {M : Type} [TopologicalSpace M] {f g : M → ℝ} {a : ℝ}
    (hsub : ∀ y, g y ≤ a ↔ f y ≤ a) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // g y ≤ a } 2 :=
  SingularHomology.homotopyEquivHomologyEquiv
    (equalCutSublevelHomeomorph hsub).toHomotopyEquiv 2

theorem MorseCancellation.equalCutSection_class {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] {f g : M → ℝ} {a : ℝ} (hsub : ∀ y, g y ≤ a ↔ f y ≤ a)
    (hlevel : ∀ y, g y = a ↔ f y = a) (γ : C((Hemisphere.Sphere 2), { y : M // f y = a })) :
    equalCutHomologyEquiv hsub (middleSectionClass γ) =
      middleSectionClass (equalCutSection hlevel γ) := by
  have hmaps :
    (equalCutSublevelHomeomorph hsub).toHomotopyEquiv.toFun.comp
        ((levelSublevelMap f le_rfl).comp γ) =
      (levelSublevelMap g le_rfl).comp (equalCutSection hlevel γ) := by
    apply ContinuousMap.ext
    intro x
    rfl
  change
    SingularMayerVietoris.singularHomologyMap
        (equalCutSublevelHomeomorph hsub).toHomotopyEquiv.toFun 2 (middleSectionClass γ) =
      _
  rw [middleSectionClass, ← LinearMap.comp_apply, ←
    SingularHomology.singularHomologyMap_comp, hmaps]
  rfl


theorem MorseCancellation.equalCutSection_trans {M : Type} [TopologicalSpace M] {f g h : M → ℝ} {a : ℝ}
    (hfg : ∀ y, g y = a ↔ f y = a) (hgh : ∀ y, h y = a ↔ g y = a)
    (γ : C((Hemisphere.Sphere 2), { y : M // f y = a })) :
    equalCutSection hgh (equalCutSection hfg γ) =
      equalCutSection (fun y => (hgh y).trans (hfg y)) γ :=
  rfl

theorem MorseCancellation.equalCutHomologyEquiv_refl {M : Type} [TopologicalSpace M] {f : M → ℝ}
    {a : ℝ} :
    equalCutHomologyEquiv (f := f) (a := a) (fun _ => Iff.rfl) =
      LinearEquiv.refl ℤ (SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2) := by
  apply LinearEquiv.ext
  intro x
  change
    SingularMayerVietoris.singularHomologyMap
        (equalCutSublevelHomeomorph (f := f) (a := a) (fun _ => Iff.rfl)).toHomotopyEquiv.toFun 2
        x =
      x
  have hmap :
    (equalCutSublevelHomeomorph (f := f) (a := a) (fun _ => Iff.rfl)).toHomotopyEquiv.toFun =
      ContinuousMap.id { y : M // f y ≤ a } :=
    rfl
  rw [hmap, SingularHomology.singularHomologyMap_id]
  rfl

theorem MorseCancellation.equalCutHomologyEquiv_trans {M : Type} [TopologicalSpace M] {f g h : M → ℝ}
    {a : ℝ} (hfg : ∀ y, g y ≤ a ↔ f y ≤ a) (hgh : ∀ y, h y ≤ a ↔ g y ≤ a) :
    (equalCutHomologyEquiv hfg).trans (equalCutHomologyEquiv hgh) =
      equalCutHomologyEquiv (fun y => (hgh y).trans (hfg y)) := by
  apply LinearEquiv.ext
  intro x
  change
    SingularMayerVietoris.singularHomologyMap
        (equalCutSublevelHomeomorph hgh).toHomotopyEquiv.toFun 2
        (SingularMayerVietoris.singularHomologyMap
          (equalCutSublevelHomeomorph hfg).toHomotopyEquiv.toFun 2 x) =
      SingularMayerVietoris.singularHomologyMap
        (equalCutSublevelHomeomorph (fun y => (hgh y).trans (hfg y))).toHomotopyEquiv.toFun 2 x
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp]
  rfl


theorem SupportedDiffeomorph.IsotopicToIdentity.homotopic {F H M : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞}
    (he : SupportedDiffeomorph.IsotopicToIdentity e) :
    (ContinuousMap.id M).Homotopic e.toHomeomorph.toHomotopyEquiv.toFun := by
  obtain ⟨A, hA, hA₀, hA₁, _⟩ := he
  exact
    ⟨{  toFun := fun p => A (p.1.val, p.2)
        continuous_toFun :=
          hA.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        map_zero_left := hA₀
        map_one_left := hA₁ }⟩

theorem SupportedDiffeomorph.IsotopicToIdentity.comp_homotopic {F H M : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞} {X : Type*}
    [TopologicalSpace X] (he : SupportedDiffeomorph.IsotopicToIdentity e) (g : C(X, M)) :
    g.Homotopic (e.toHomeomorph.toHomotopyEquiv.toFun.comp g) := by
  simpa using he.homotopic.comp (ContinuousMap.Homotopic.refl g)

theorem SupportedDiffeomorph.IsotopicToIdentity.conj {V H X Y : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [TopologicalSpace H] {J : ModelWithCorners ℝ V H} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H Y] (e : Diffeomorph J J X Y ∞)
    (D : Diffeomorph J J X X ∞) (hD : SupportedDiffeomorph.IsotopicToIdentity D) :
    SupportedDiffeomorph.IsotopicToIdentity (e.symm.trans (D.trans e)) := by
  obtain ⟨A, hA, hzero, hone, hslices⟩ := hD
  refine
    ⟨fun z : ℝ × Y => e (A (z.1, e.symm z.2)),
      e.contMDiff.comp (hA.comp (contMDiff_fst.prodMk (e.symm.contMDiff.comp contMDiff_snd))), ?_,
      ?_, ?_⟩
  · intro y
    change e (A (0, e.symm y)) = y
    rw [hzero, e.apply_symm_apply]
  · intro y
    change e (A (1, e.symm y)) = e (D (e.symm y))
    rw [hone]
  · intro t
    obtain ⟨Dt, hDt⟩ := hslices t
    refine ⟨e.symm.trans (Dt.trans e), ?_⟩
    intro y
    change e (A (t, e.symm y)) = e (Dt (e.symm y))
    rw [hDt]

theorem Set.ncard_range_comp_inter_range_comp_of_injective {A B X Y : Type*} (e : X → Y)
    (he : Function.Injective e) (α : A → X) (β : B → X) :
    (Set.range (e ∘ α) ∩ Set.range (e ∘ β)).ncard = (Set.range α ∩ Set.range β).ncard := by
  have hset : Set.range (e ∘ α) ∩ Set.range (e ∘ β) = e '' (Set.range α ∩ Set.range β) := by
    ext y
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have hab : α a = β b := he (ha.trans hb.symm)
      exact ⟨α a, ⟨Set.mem_range_self a, ⟨b, hab.symm⟩⟩, ha⟩
    · rintro ⟨x, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hx⟩
      exact ⟨⟨a, (congrArg e ha).trans hx⟩, ⟨b, (congrArg e hb).trans hx⟩⟩
  rw [hset]
  exact Set.ncard_image_of_injective _ he


end
