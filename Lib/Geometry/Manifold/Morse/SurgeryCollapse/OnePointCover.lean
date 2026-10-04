/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.LinearSphereAction
import Lib.AlgebraicTopology.SingularHomology.LocalDegree
import Lib.AlgebraicTopology.SingularHomology.OnePointCover
import Lib.AlgebraicTopology.SingularHomology.Suspension
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence

/-!
# The one-point compactification of `ℝⁿ` covered by two contractible patches

The one-point compactification `OnePoint N` of a finite-dimensional normed space is a sphere;
removing a point leaves a space homeomorphic to `ℝⁿ` (`OnePointCover.punctureHomeomorph`, via
Mathlib's stereographic projection `stereographic'`), so the two patches
`OnePoint N ∖ {0}` and `OnePoint N ∖ {∞}` of `Lib.AlgebraicTopology.SingularHomology.OnePointCover`
are contractible (`oldPatch_contractible`, `finitePatch_contractible`) and their overlap
`N ∖ {0}` is homotopy equivalent to the unit sphere (`overlapHomeomorph`, `overlapSphereEquiv`).
Mayer–Vietoris then gives the suspension isomorphism
`H_{k+2}(OnePoint N) ≅ H_{k+1}(S(N))` (`sphereHomologyEquiv`) with an injective connecting map
`sphereConnecting`, cf. Hatcher, *Algebraic Topology*, Exercise 2.2.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

/-- `Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1)`, used as a local instance for the
stereographic charts of the sphere. -/
theorem OnePointCover.instLocal1 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

attribute [local instance] OnePointCover.instLocal1 in
private def OnePointCover.spherePunctureHomeomorph (n : ℕ)
    (a : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ↥({ a }ᶜ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ≃ₜ
      EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source (n := n) a).symm).trans
    ((stereographic' n a).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target a)).trans (Homeomorph.Set.univ _)))

attribute [local instance] OnePointCover.instLocal1 in
/-- The complement of a point `a` in the one-point compactification of a finite-dimensional normed
space `N` is homeomorphic to `EuclideanSpace ℝ (Fin (finrank ℝ N))`, by stereographic projection
from `a` on the sphere `OnePoint N ≃ₜ S^{dim N}`. -/
def OnePointCover.punctureHomeomorph {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (a : OnePoint N) :
    ↥({ a }ᶜ : Set (OnePoint N)) ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ N)) := by
  let e : OnePoint N ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ N + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  let es : ↥({ a }ᶜ : Set (OnePoint N)) ≃ₜ ↥({e a}ᶜ : Set _) :=
    e.subtype
      (fun x => by
        change x ≠ a ↔ e x ≠ e a
        exact e.injective.ne_iff.symm)
  exact es.trans (spherePunctureHomeomorph _ (e a))

attribute [local instance] OnePointCover.instLocal1 in
/-- `OnePointCover.oldPatch = OnePoint N ∖ {0}` is contractible. -/
theorem OnePointCover.oldPatch_contractible {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] : ContractibleSpace (oldPatch (N := N)) :=
  (punctureHomeomorph ((0 : N) : OnePoint N)).contractibleSpace

attribute [local instance] OnePointCover.instLocal1 in
/-- `OnePointCover.finitePatch = OnePoint N ∖ {∞}` is contractible. -/
theorem OnePointCover.finitePatch_contractible {N : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] : ContractibleSpace (finitePatch (N := N)) :=
  (punctureHomeomorph (OnePoint.infty : OnePoint N)).contractibleSpace

attribute [local instance] OnePointCover.instLocal1 in
/-- The overlap `oldPatch ∩ finitePatch` consists of finite points `(x : N)`. -/
theorem OnePointCover.overlap_subset_range {N : Type*} [NormedAddCommGroup N] :
    oldPatch (N := N) ∩ finitePatch ⊆ Set.range (OnePoint.some : N → _) := by
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact (hx.2 rfl).elim
  | coe x => exact ⟨x, rfl⟩

attribute [local instance] OnePointCover.instLocal1 in
/-- The preimage of `oldPatch ∩ finitePatch` under `N → OnePoint N` is `{u | u ≠ 0}`. -/
theorem OnePointCover.overlap_preimage {N : Type*} [NormedAddCommGroup N] :
    (OnePoint.some : N → OnePoint N) ⁻¹' (oldPatch ∩ finitePatch) = {u : N | u ≠ 0} := by
  ext x
  change ((x : OnePoint N) ≠ ((0 : N) : OnePoint N) ∧ (x : OnePoint N) ≠ OnePoint.infty) ↔ x ≠ 0
  constructor
  · rintro ⟨h, -⟩ hx
    exact h (congrArg (OnePoint.some : N → OnePoint N) hx)
  · intro hx
    exact ⟨fun h => hx (OnePoint.coe_injective h), OnePoint.coe_ne_infty x⟩

attribute [local instance] OnePointCover.instLocal1 in
/-- The homeomorphism `N ∖ {0} ≃ₜ oldPatch ∩ finitePatch`, `u ↦ (u : OnePoint N)`. -/
def OnePointCover.overlapHomeomorph {N : Type*} [NormedAddCommGroup N] :
    PuncturedRadial.Space N ≃ₜ ↥(oldPatch (N := N) ∩ finitePatch) :=
  (Homeomorph.setCongr overlap_preimage.symm).trans
    (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphOfSubsetRange overlap_subset_range)

attribute [local instance] OnePointCover.instLocal1 in
/-- `overlapHomeomorph u = (u : OnePoint N)` as points of `OnePoint N`. -/
theorem OnePointCover.overlapHomeomorph_apply {N : Type*} [NormedAddCommGroup N]
    (u : PuncturedRadial.Space N) : (overlapHomeomorph u).val = (u.val : OnePoint N) :=
  rfl

attribute [local instance] OnePointCover.instLocal1 in
/-- The homotopy equivalence `S(N) ≃ₕ oldPatch ∩ finitePatch` through the sphere of radius `r > 0`
in `N ∖ {0}`. -/
def OnePointCover.overlapSphereEquiv {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) : Metric.sphere (0 : N) 1 ≃ₕ ↥(oldPatch (N := N) ∩ finitePatch) :=
  (PuncturedRadial.sphereHomotopyEquiv r hr).trans overlapHomeomorph.toHomotopyEquiv

/-- The homology isomorphism `H_k(S(N)) ≃ H_k(oldPatch ∩ finitePatch)` induced by
`overlapSphereEquiv r hr`. -/
def OnePointCover.overlapHomologyEquiv {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (↥(oldPatch (N := N) ∩ finitePatch)) k :=
  SingularHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv r hr) k

/-- The connecting homomorphism `H_{k+1}(OnePoint N) → H_k(S(N))` of the two-patch cover, the
Mayer–Vietoris connecting map followed by `(overlapHomologyEquiv r hr k)⁻¹`. -/
def OnePointCover.sphereConnecting {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (OnePoint N) (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) k :=
  (overlapHomologyEquiv r hr k).symm.toLinearMap.comp
    (SingularMayerVietoris.connectingHomomorphism oldPatch finitePatch oldPatch_open
      finitePatch_open cover k)

/-- For finite-dimensional `N`, `sphereConnecting r hr k : H_{k+1}(OnePoint N) → H_k(S(N))` is
injective (both patches are contractible). -/
theorem OnePointCover.sphereConnecting_injective {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N] (r : ℝ) (hr : 0 < r) (k : ℕ) :
    Function.Injective (sphereConnecting (N := N) r hr k) := by
  let : ContractibleSpace (oldPatch (N := N)) := oldPatch_contractible
  let : ContractibleSpace (finitePatch (N := N)) := finitePatch_contractible
  have hi :
    Function.Injective
      (SingularMayerVietoris.connectingHomomorphism (oldPatch (N := N)) finitePatch oldPatch_open
        finitePatch_open cover k) :=
    Suspension.contractibleCoverConnecting_injective (oldPatch (N := N)) finitePatch
      oldPatch_open finitePatch_open cover k
  exact (overlapHomologyEquiv (N := N) r hr k).symm.injective.comp hi

/-- The suspension isomorphism `H_{k+2}(OnePoint N) ≃ H_{k+1}(S(N))` for finite-dimensional `N`,
from the Mayer–Vietoris sequence of the cover by two contractible patches. -/
def OnePointCover.sphereHomologyEquiv {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (OnePoint N) (k + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) (k + 1) := by
  let : ContractibleSpace (oldPatch (N := N)) := oldPatch_contractible
  let : ContractibleSpace (finitePatch (N := N)) := finitePatch_contractible
  exact
    (Suspension.contractibleCoverHomologyHigherEquiv oldPatch finitePatch oldPatch_open
          finitePatch_open cover k).trans
      (overlapHomologyEquiv r hr (k + 1)).symm

end
