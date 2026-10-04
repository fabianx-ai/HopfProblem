/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Lib.AlgebraicTopology.SingularHomology.OnePointCover
import Lib.Geometry.Manifold.Morse.BeltCancellation
import Lib.Geometry.Manifold.Morse.Handle
import Lib.Geometry.Manifold.Morse.Reeb
import Lib.Geometry.Manifold.Morse.SublevelSets
import Lib.Geometry.Manifold.Morse.SurgeryHomology
import Lib.Geometry.Manifold.RegularLevel
import Lib.Topology.Homotopy.CellAttachment
import Lib.Geometry.Manifold.Morse.OrderedCancellation.PathComponents
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence

/-!
# The homology exact sequence of passing a critical point

Passing a critical point of index `λ` attaches a `λ`-cell to the sublevel set (Milnor, *Morse
Theory*, Theorem 3.2); the cell exact sequence of
`Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence` transported along the core-cell
presentation of a Morse surgery datum gives the exact sequence
`… → H_{k+1}(M_{upper}) → H_k(S^{λ-1}) → H_k(M_{lower}) → H_k(M_{upper}) → …`
(`ManifoldMorse.MorseSurgeryData.morse_exact_at_lower`, `morse_exact_at_upper`,
`morse_exact_at_attachingSphere`, with connecting map `morseConnectingMap`).  Consequences for
`λ ≥ 2`: `H₀` and `H₁` do not change (`MorseCancellation.native_lowerRealization_zero_bijective`,
`lowerRealization_one_surjective`), path-connectedness passes downward
(`native_lower_pathConnected_of_upper`), and `H₁` of a sublevel set vanishes when all handles
below have index `≥ 2` (`ManifoldMorse.SurgeryWindows.lower_homologyOne_subsingleton_of_indices`);
below an index-`0` handle the sublevel set is empty when the upper one is path-connected
(`native_zero_handle_lower_isEmpty`).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- The homology isomorphism `H_k({f ≤ f p - r²}) ≃ H_k((coreCellPresentation hf).old)` induced by
the homeomorphism `d.cellOldHomeomorph hf`. -/
def ManifoldMorse.MorseSurgeryData.cellOldHomologyEquiv {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (k : ℕ) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (d.coreCellPresentation hf).old k :=
  SingularHomology.homeomorphHomologyEquiv (d.cellOldHomeomorph hf) k

attribute [local instance 100] Classical.propDecidable in
/-- The homology isomorphism `H_k({f ≤ f p - r²} ∪ range coreMap) ≃ H_k({f ≤ f p + r²})` induced
by the homotopy equivalence `d.coreUnionHomotopyEquiv hf`. -/
def ManifoldMorse.MorseSurgeryData.cellTotalHomologyEquiv {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology
        (↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap)) k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k :=
  SingularHomology.homotopyEquivHomologyEquiv (d.coreUnionHomotopyEquiv hf) k

attribute [local instance 100] Classical.propDecidable in
/-- The map `H_k(S(N)) → H_k({f ≤ f p - r²})` induced by the core boundary map
`d.coreBoundaryMap` (the attaching sphere of the handle). -/
def ManifoldMorse.MorseSurgeryData.coreBoundaryHomologyMap {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k :=
  SingularMayerVietoris.singularHomologyMap d.coreBoundaryMap k

attribute [local instance 100] Classical.propDecidable in
/-- The map `H_k({f ≤ f p - r²}) → H_k({f ≤ f p + r²})` induced by the inclusion
`d.realizedLowerInclusion`. -/
def ManifoldMorse.MorseSurgeryData.lowerRealizationHomologyMap {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (k : ℕ) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k :=
  SingularMayerVietoris.singularHomologyMap d.realizedLowerInclusion k

attribute [local instance 100] Classical.propDecidable in
/-- The connecting homomorphism `H_{k+1}({f ≤ f p + r²}) → H_k(S(N))` of the Morse surgery `d`:
the cell connecting map of the core cell presentation, transported by
`(cellTotalHomologyEquiv hf (k + 1))⁻¹`. -/
def ManifoldMorse.MorseSurgeryData.morseConnectingMap {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f) (k : ℕ) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } (k + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k :=
  ((d.coreCellPresentation hf).cellConnectingMap k).comp
    (d.cellTotalHomologyEquiv hf (k + 1)).symm.toLinearMap

attribute [local instance 100] Classical.propDecidable in
/-- The attaching map of the core cell presentation on `H_k` is `coreBoundaryHomologyMap k`
followed by `cellOldHomologyEquiv hf k`. -/
theorem ManifoldMorse.MorseSurgeryData.cellAttachingHomology_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        k) :
    (d.coreCellPresentation hf).attachingHomologyMap k a =
      d.cellOldHomologyEquiv hf k (d.coreBoundaryHomologyMap k a) := by
  change
    SingularMayerVietoris.singularHomologyMap (d.coreCellPresentation hf).attachingSphere k a =
      SingularMayerVietoris.singularHomologyMap (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun k
        (SingularMayerVietoris.singularHomologyMap d.coreBoundaryMap k a)
  rw [d.coreCell_attaching_eq, SingularHomology.singularHomologyMap_comp]
  rfl

attribute [local instance 100] Classical.propDecidable in
/-- `cellTotalHomologyEquiv hf k ∘ oldHomologyMap k ∘ cellOldHomologyEquiv hf k` is
`lowerRealizationHomologyMap k`. -/
theorem ManifoldMorse.MorseSurgeryData.cellOldHomology_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k) :
    d.cellTotalHomologyEquiv hf k
        ((d.coreCellPresentation hf).oldHomologyMap k (d.cellOldHomologyEquiv hf k a)) =
      d.lowerRealizationHomologyMap k a := by
  change
    SingularMayerVietoris.singularHomologyMap (d.coreUnionHomotopyEquiv hf).toFun k
        (SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (d.coreCellPresentation hf).old) k
          (SingularMayerVietoris.singularHomologyMap
            (d.cellOldHomeomorph hf).toHomotopyEquiv.toFun k a)) =
      SingularMayerVietoris.singularHomologyMap d.realizedLowerInclusion k a
  rw [← LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp, ←
    LinearMap.comp_apply, ← SingularHomology.singularHomologyMap_comp]
  rfl

attribute [local instance 100] Classical.propDecidable in
/-- `morseConnectingMap hf k` on `cellTotalHomologyEquiv hf (k + 1) a` is the cell connecting map
of the core cell presentation on `a`. -/
theorem ManifoldMorse.MorseSurgeryData.morseConnecting_compare {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ↥({y : M | f y ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) (k + 1)) :
    d.morseConnectingMap hf k (d.cellTotalHomologyEquiv hf (k + 1) a) =
      (d.coreCellPresentation hf).cellConnectingMap k a := by
  change
    (d.coreCellPresentation hf).cellConnectingMap k
        ((d.cellTotalHomologyEquiv hf (k + 1)).symm (d.cellTotalHomologyEquiv hf (k + 1) a)) =
      _
  rw [LinearEquiv.symm_apply_apply]

attribute [local instance 100] Classical.propDecidable in
/-- Exactness at `H_k(M_{lower})`, `k ≠ 0`: the image of `coreBoundaryHomologyMap k` is the kernel
of `lowerRealizationHomologyMap k`. -/
theorem ManifoldMorse.MorseSurgeryData.morse_exact_at_lower {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (d.coreBoundaryHomologyMap k) =
      LinearMap.ker (d.lowerRealizationHomologyMap k) := by
  refine
    HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
      (d.cellOldHomologyEquiv hf k).symm (d.cellTotalHomologyEquiv hf k)
      ((d.coreCellPresentation hf).attachingHomologyMap k)
      ((d.coreCellPresentation hf).oldHomologyMap k) (d.coreBoundaryHomologyMap k)
      (d.lowerRealizationHomologyMap k) ?_ ?_ ((d.coreCellPresentation hf).cell_exact_at_old k hk)
  · intro a
    change
      d.coreBoundaryHomologyMap k a =
        (d.cellOldHomologyEquiv hf k).symm ((d.coreCellPresentation hf).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]
  · intro a
    have h := d.cellOldHomology_compare hf k ((d.cellOldHomologyEquiv hf k).symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

attribute [local instance 100] Classical.propDecidable in
/-- Exactness at `H_{k+1}(M_{upper})`: the image of `lowerRealizationHomologyMap (k + 1)` is the
kernel of `morseConnectingMap hf k`. -/
theorem ManifoldMorse.MorseSurgeryData.morse_exact_at_upper {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) :
    LinearMap.range (d.lowerRealizationHomologyMap (k + 1)) =
      LinearMap.ker (d.morseConnectingMap hf k) := by
  refine
    HomologyTransport.exact_of_equivalences (d.cellOldHomologyEquiv hf (k + 1)).symm
      (d.cellTotalHomologyEquiv hf (k + 1)) (LinearEquiv.refl ℤ _)
      ((d.coreCellPresentation hf).oldHomologyMap (k + 1))
      ((d.coreCellPresentation hf).cellConnectingMap k) (d.lowerRealizationHomologyMap (k + 1))
      (d.morseConnectingMap hf k) ?_ ?_ ((d.coreCellPresentation hf).cell_exact_at_ambient k)
  · intro a
    have h := d.cellOldHomology_compare hf (k + 1) ((d.cellOldHomologyEquiv hf (k + 1)).symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · exact d.morseConnecting_compare hf k

attribute [local instance 100] Classical.propDecidable in
/-- Exactness at `H_k(S(N))`, `k ≠ 0`: the image of `morseConnectingMap hf k` is the kernel of
`coreBoundaryHomologyMap k`. -/
theorem ManifoldMorse.MorseSurgeryData.morse_exact_at_attachingSphere {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (d.morseConnectingMap hf k) = LinearMap.ker (d.coreBoundaryHomologyMap k) := by
  refine
    HomologyTransport.exact_of_equivalences (d.cellTotalHomologyEquiv hf (k + 1))
      (LinearEquiv.refl ℤ _) (d.cellOldHomologyEquiv hf k).symm
      ((d.coreCellPresentation hf).cellConnectingMap k)
      ((d.coreCellPresentation hf).attachingHomologyMap k) (d.morseConnectingMap hf k)
      (d.coreBoundaryHomologyMap k) ?_ ?_ ((d.coreCellPresentation hf).cell_exact_at_sphere k hk)
  · exact d.morseConnecting_compare hf k
  · intro a
    change
      d.coreBoundaryHomologyMap k a =
        (d.cellOldHomologyEquiv hf k).symm ((d.coreCellPresentation hf).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]

attribute [local instance 100] Classical.propDecidable in
/-- For `k ≠ 0`, if `H_k(M_{upper})` and `H_k(S(N))` are subsingletons then so is
`H_k(M_{lower})`. -/
theorem ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_sphere
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k)]
    [Subsingleton
        (SingularMayerVietoris.SingularHomology
          (Metric.sphere (0 : d.chart.NegativeCoordinates) 1) k)] :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k) := by
  have hall :
    ∀ a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k, a = 0 :=
    by
    intro a
    have ha : a ∈ LinearMap.ker (d.lowerRealizationHomologyMap k) := Subsingleton.elim _ _
    rw [← d.morse_exact_at_lower hf k hk] at ha
    obtain ⟨s, hs⟩ := ha
    have hs0 : s = 0 := Subsingleton.elim _ _
    rw [hs0, map_zero] at hs
    exact hs.symm
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

/-- If the index of `d` is at least `2`, the connecting map `H₁(M_{upper}) → H₀(S(N))` is zero. -/
theorem ManifoldMorse.MorseSurgeryData.morseConnecting_zero_apply {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (a : SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 1) :
    d.morseConnectingMap hf 0 a = 0 := by
  let := d.attachingSphere_pathConnected hindex
  exact (d.coreCellPresentation hf).cellConnecting_zero_apply _

/-- If the index of `d` is at least `2`, `H₁(M_{lower}) → H₁(M_{upper})` is surjective. -/
theorem ManifoldMorse.MorseSurgeryData.lowerRealization_one_surjective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    Function.Surjective (d.lowerRealizationHomologyMap 1) := by
  intro a
  have ha : a ∈ LinearMap.ker (d.morseConnectingMap hf 0) :=
    d.morseConnecting_zero_apply hf hindex a
  rw [← d.morse_exact_at_upper hf 0] at ha
  exact ha

/-- If the index of `d` is at least `2` and `H₁(M_{lower})` is a subsingleton, so is
`H₁(M_{upper})`. -/
theorem ManifoldMorse.MorseSurgeryData.upperHomologyOne_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)] :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 1) :=
  (d.lowerRealization_one_surjective hf hindex).subsingleton

/-- If the index of `d` is at least `2`, `H₀(M_{lower}) → H₀(M_{upper})` is bijective. -/
theorem MorseCancellation.native_lowerRealization_zero_bijective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates) :
    Function.Bijective (d.lowerRealizationHomologyMap 0) := by
  let := d.attachingSphere_pathConnected hindex
  have hi := cell_oldHomologyMap_zero_bijective (d.coreCellPresentation hf)
  have heq :
    d.lowerRealizationHomologyMap 0 =
      (d.cellTotalHomologyEquiv hf 0).toLinearMap.comp
        (((d.coreCellPresentation hf).oldHomologyMap 0).comp
          (d.cellOldHomologyEquiv hf 0).toLinearMap) := by
    ext a
    exact (d.cellOldHomology_compare hf 0 a).symm
  rw [heq]
  exact
    (d.cellTotalHomologyEquiv hf 0).bijective.comp
      (hi.comp (d.cellOldHomologyEquiv hf 0).bijective)

/-- If the index of `d` is at least `2` and the upper sublevel set is path-connected, so is the
lower one. -/
theorem MorseCancellation.native_lower_pathConnected_of_upper {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    [PathConnectedSpace { z : M // f z ≤ f p + d.radius ^ 2 }] :
    PathConnectedSpace { z : M // f z ≤ f p - d.radius ^ 2 } := by
  let := d.attachingSphere_pathConnected hindex
  let : Nonempty { z : M // f z ≤ f p - d.radius ^ 2 } :=
    ⟨d.coreBoundaryMap (Classical.arbitrary (Metric.sphere (0 : d.chart.NegativeCoordinates) 1))⟩
  exact
    pathConnectedSpace_of_homologyZero_injective d.realizedLowerInclusion
      (native_lowerRealization_zero_bijective d hf hindex).1

/-- If the index of `d` is `0` and the upper sublevel set `{f ≤ f p + r²}` is path-connected,
the lower sublevel set `{f ≤ f p - r²}` is empty. -/
theorem MorseCancellation.native_zero_handle_lower_isEmpty {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0)
    [PathConnectedSpace { z : M // f z ≤ f p + d.radius ^ 2 }] :
    IsEmpty { z : M // f z ≤ f p - d.radius ^ 2 } := by
  let : Subsingleton d.chart.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ d.chart.NegativeCoordinates).mp hindex
  let : IsEmpty (Metric.sphere (0 : d.chart.NegativeCoordinates) 1) :=
    ⟨fun v => by
      have h := mem_sphere_zero_iff_norm.mp v.property
      rw [Subsingleton.elim v.val 0, norm_zero] at h
      norm_num at h⟩
  let : PathConnectedSpace ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) :=
    pathConnectedSpace_of_homotopyEquiv (d.coreUnionHomotopyEquiv hf)
  have he := cell_old_empty_of_empty_boundary (d.coreCellPresentation hf)
  refine ⟨fun x => ?_⟩
  have hx := (d.cellOldHomeomorph hf x).property
  exact (Set.eq_empty_iff_forall_notMem.mp he) _ hx

/-- If every core boundary point `d.coreBoundaryMap u` is joined in the lower sublevel set to the
point `a`, and the upper sublevel set is path-connected, then the lower sublevel set is
path-connected. -/
theorem MorseCancellation.native_lower_pathConnected_of_attaching_component {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (a : { z : M // f z ≤ f p - d.radius ^ 2 }) (hcomponent : ∀ u, Joined (d.coreBoundaryMap u) a)
    [PathConnectedSpace { z : M // f z ≤ f p + d.radius ^ 2 }] :
    PathConnectedSpace { z : M // f z ≤ f p - d.radius ^ 2 } := by
  let : PathConnectedSpace ↥({z : M | f z ≤ f p - d.radius ^ 2} ∪ Set.range d.coreMap) :=
    pathConnectedSpace_of_homotopyEquiv (d.coreUnionHomotopyEquiv hf)
  let : PathConnectedSpace (d.coreCellPresentation hf).old :=
    cell_old_pathConnected_of_attaching_component (d.coreCellPresentation hf)
      (d.cellOldHomeomorph hf a)
      (fun u => by
        rw [d.coreCell_attaching_eq]
        exact (hcomponent u).map (d.cellOldHomeomorph hf).continuous)
  exact pathConnectedSpace_of_homotopyEquiv (d.cellOldHomeomorph hf).toHomotopyEquiv

/-- If the index of `d` is positive and any two core boundary points are joined in the lower
sublevel set, there is a point `a` of the lower sublevel set joined to every core boundary point. -/
theorem MorseCancellation.native_attaching_component_of_pairwise_joined {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hindex : 0 < Module.finrank ℝ d.chart.NegativeCoordinates)
    (hjoined : ∀ u v, Joined (d.coreBoundaryMap u) (d.coreBoundaryMap v)) :
    ∃ a : { z : M // f z ≤ f p - d.radius ^ 2 }, ∀ u, Joined (d.coreBoundaryMap u) a := by
  let : Nontrivial d.chart.NegativeCoordinates := Module.nontrivial_of_finrank_pos hindex
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : d.chart.NegativeCoordinates) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  exact ⟨d.coreBoundaryMap ⟨v, hv⟩, fun u => hjoined u ⟨v, hv⟩⟩

/-- The homology isomorphism `H_k({f ≤ upper i}) ≃ H_k({f ≤ lower j})` induced by the sublevel
homeomorphism of a band datum `D : S.BandData i j`. -/
def ManifoldMorse.SurgeryWindows.BandData.homologyEquiv {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {S : ManifoldMorse.SurgeryWindows E f} {i j : Fin S.count} (D : S.BandData i j)
    (k : ℕ) :
    SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point i) } k ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.point j) } k :=
  SingularHomology.homeomorphHomologyEquiv D.sublevelHomeomorph k

/-- If every window strictly between the first and the `j`-th window of `S` has index at least
`2`, then `H₁({f ≤ lower (point j)})` is a subsingleton. -/
theorem ManifoldMorse.SurgeryWindows.lower_homologyOne_subsingleton_of_indices {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (j : Fin S.count) (hj : 0 < j.val)
    (hindex :
      ∀ i : Fin S.count,
        0 < i.val →
          i.val < j.val → 2 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.lower (S.point j) } 1) := by
  have hupper :
    ∀ n : ℕ,
      ∀ hn : n < S.count,
        n < j.val →
          Subsingleton
            (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨n, hn⟩) }
              1) := by
    intro n
    induction n with
    | zero =>
      intro hn _
      obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hn
      exact D.homology_subsingleton 1 one_ne_zero
    | succ n ih =>
      intro hn hnj
      have hn' : n < S.count := by omega
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨n, hn'⟩) + (S.data (S.point ⟨n, hn'⟩)).radius ^ 2 } 1) :=
        ih hn' (by omega)
      obtain ⟨T, _, hT, _⟩ := S.exists_consecutiveBandBridge hf ⟨n, hn'⟩ ⟨n + 1, hn⟩ rfl
      let H :=
        (S.data (S.point ⟨n, hn'⟩)).bandSublevelHomeomorph (S.data (S.point ⟨n + 1, hn⟩))
          T.toHomeomorph hT
      let :
        Subsingleton
          (SingularMayerVietoris.SingularHomology
            { x : M // f x ≤ f (S.point ⟨n + 1, hn⟩) - (S.data (S.point ⟨n + 1, hn⟩)).radius ^ 2 }
            1) :=
        (SingularHomology.homeomorphHomologyEquiv H.symm 1).injective.subsingleton
      exact
        (S.data (S.point ⟨n + 1, hn⟩)).upperHomologyOne_subsingleton hf.continuous
          (hindex ⟨n + 1, hn⟩ (Nat.succ_pos n) hnj)
  have hp : j.val - 1 < S.count := by omega
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { x : M //
          f x ≤ f (S.point ⟨j.val - 1, hp⟩) + (S.data (S.point ⟨j.val - 1, hp⟩)).radius ^ 2 }
        1) :=
    hupper (j.val - 1) hp (by omega)
  obtain ⟨T, _, hT, _⟩ :=
    S.exists_consecutiveBandBridge hf ⟨j.val - 1, hp⟩ j (by change j.val - 1 + 1 = j.val; omega)
  let H :=
    (S.data (S.point ⟨j.val - 1, hp⟩)).bandSublevelHomeomorph (S.data (S.point j)) T.toHomeomorph
      hT
  exact (SingularHomology.homeomorphHomologyEquiv H.symm 1).injective.subsingleton

/-- For `k ≠ 0`, if the index `λ` of `d` satisfies `2 ≤ λ` and `λ ≠ k + 1`, and `H_k(M_{upper})` is
a subsingleton, then `H_k(M_{lower})` is a subsingleton. -/
theorem ManifoldMorse.MorseSurgeryData.lowerHomology_subsingleton_of_upper_and_index
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [T2Space M] {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    (hindex : 2 ≤ Module.finrank ℝ d.chart.NegativeCoordinates)
    (hne : Module.finrank ℝ d.chart.NegativeCoordinates ≠ k + 1)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } k)] :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } k) := by
  let := d.attachingHomology_subsingleton_of_index k hk hindex hne
  exact d.lowerHomology_subsingleton_of_upper_and_sphere hf k hk

end
