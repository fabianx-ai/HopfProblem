/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
import Mathlib
import Lib.Algebra.Module.IntegerPresentation
import Lib.Analysis.Calculus.MorseLemma
import Lib.Geometry.Manifold.Morse.SurgeryHomology
import Lib.Geometry.Manifold.Morse.SurgeryWindows
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.CellExactSequence
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.HandleCollapse
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.HandleExactSequence
import Lib.Geometry.Manifold.Morse.SurgeryCollapse.SphereOrientation

/-!
# The index-two basis and the index-three presentation of `H₂` (proof-specific)

Proof-specific material of the six-sphere formalization; not library mathematics and not
registered in `Lib.lean`.  Every statement is pinned to the indices `2` and `3` of the W4W1
argument: each index-`2` window adds a free generator to `H₂` of the sublevel set, read off by the
collapse coordinate (`ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate`,
`ManifoldMorse.SurgeryWindows.indexTwoBasis`), and each index-`3` window adds one relation, the
class of its attaching sphere (`indexThreeAttachingClass`, `indexThreePresentation`); over an
index-`2` prefix followed by an index-`3` block this yields the integer presentation
`ManifoldMorse.SurgeryWindows.middlePresentation` with matrix `middleMatrix`.

Moved from `Lib.Geometry.Manifold.Morse.SurgeryCollapse`; statements unchanged.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ContinuousMap

noncomputable section

def ManifoldMorse.MorseSurgeryData.indexTwoCollapseCoordinate {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2 →ₗ[ℤ] ℤ :=
  (SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)).toLinearMap.comp
    (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) 2)

theorem ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_surjective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)] :
    Function.Surjective (d.indexTwoCollapseCoordinate hf hindex) :=
  (SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)).surjective.comp
    (d.upperCollapse_surjective_of_lower hf 0)

theorem ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_kernel {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    LinearMap.ker (d.indexTwoCollapseCoordinate hf hindex) =
      LinearMap.range (d.lowerRealizationHomologyMap 2) := by
  rw [← d.upperCollapse_homology_kernel hf 1]
  ext a
  let C := SpherePoint.targetCountMark 0 (d.indexTwoNormalModel hindex)
  change
    C (SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) 2 a) = 0 ↔
      SingularMayerVietoris.singularHomologyMap (d.upperCollapseMap hf) 2 a = 0
  constructor
  · intro h
    exact C.injective (h.trans (map_zero C).symm)
  · intro h
    rw [h, map_zero]

theorem ManifoldMorse.MorseSurgeryData.lowerRealization_two_injective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2) :
    Function.Injective (d.lowerRealizationHomologyMap 2) := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2) :=
    d.attachingHomology_subsingleton_of_index 2 (by norm_num) (by omega) (by omega)
  apply LinearMap.ker_eq_bot.mp
  rw [← d.morse_exact_at_lower hf 2 (by norm_num)]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  change d.coreBoundaryHomologyMap 2 a = 0
  rw [Subsingleton.elim a 0, map_zero]

theorem ManifoldMorse.MorseSurgeryData.exists_indexTwoHomology_split {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)] :
    ∃ H :
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2 × ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2,
      (∀ a, H (a, 0) = d.lowerRealizationHomologyMap 2 a) ∧
        ∀ z, d.indexTwoCollapseCoordinate hf hindex (H z) = z.2 := by
  obtain ⟨H, hH, hcoord⟩ :=
    LinearMap.exists_prodAddEquiv_of_functional_ker_eq_range (d.lowerRealizationHomologyMap 2)
      (d.indexTwoCollapseCoordinate hf hindex) (d.lowerRealization_two_injective hf hindex)
      (d.indexTwoCoordinate_surjective hf hindex) (d.indexTwoCoordinate_kernel hf hindex)
  exact ⟨H.toIntLinearEquiv, hH, hcoord⟩

theorem ManifoldMorse.MorseSurgeryData.exists_indexTwoBasis_extension {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 1)]
    (n : ℕ)
    (e :
      (Fin n → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2) :
    ∃ H :
      (Fin (n + 1) → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2,
      (∀ v, H (Fin.cons 0 v) = d.lowerRealizationHomologyMap 2 (e v)) ∧
        ∀ v, d.indexTwoCollapseCoordinate hf hindex (H v) = v 0 := by
  obtain ⟨H, hH, hcoord⟩ := d.exists_indexTwoHomology_split hf hindex
  let G :=
    (((Fin.consLinearEquiv ℤ fun _ : Fin (n + 1) => ℤ).symm.trans
          (LinearEquiv.prodComm ℤ ℤ (Fin n → ℤ))).toAddEquiv).trans
      ((e.toAddEquiv.prodCongr (AddEquiv.refl ℤ)).trans H.toAddEquiv)
  refine ⟨G.toIntLinearEquiv, ?_, ?_⟩
  · intro v
    exact hH (e v)
  · intro v
    exact hcoord (e (fun i => v i.succ), v 0)

theorem ManifoldMorse.SurgeryWindows.indexTwoBasis_step {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    (hn : n + 1 < S.count) (hpre : S.HasIndexTwoPrefix (n + 1))
    (e :
      (Fin n → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology
          { x : M // f x ≤ S.upper (S.point ⟨n, Nat.lt_of_succ_lt hn⟩) } 2) :
    let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
    ∃ H :
      (Fin (n + 1) → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨n + 1, hn⟩) } 2,
      (∀ v,
          H (Fin.cons 0 v) =
            (S.data (S.point ⟨n + 1, hn⟩)).lowerRealizationHomologyMap 2
              (B.homologyEquiv 2 (e v))) ∧
        ∀ v,
          (S.data (S.point ⟨n + 1, hn⟩)).indexTwoCollapseCoordinate hf.continuous
              (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) le_rfl) (H v) =
            v 0 := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { x : M // f x ≤ f (S.point ⟨n + 1, hn⟩) - (S.data (S.point ⟨n + 1, hn⟩)).radius ^ 2 }
        1) :=
    S.lower_homologyOne_subsingleton_of_indices hf ⟨n + 1, hn⟩ (Nat.succ_pos n)
      (fun i hi hin => by
        have h := hpre i hi (Nat.le_of_lt hin)
        omega)
  let B := S.consecutiveBandData hf ⟨n, Nat.lt_of_succ_lt hn⟩ ⟨n + 1, hn⟩ rfl
  exact
    (S.data (S.point ⟨n + 1, hn⟩)).exists_indexTwoBasis_extension hf.continuous
      (hpre ⟨n + 1, hn⟩ (Nat.succ_pos n) le_rfl) n (e.trans (B.homologyEquiv 2))

def ManifoldMorse.SurgeryWindows.indexTwoBasis {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    (n : ℕ) →
      (hn : n < S.count) →
        S.HasIndexTwoPrefix n →
          (Fin n → ℤ) ≃ₗ[ℤ]
            SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨n, hn⟩) } 2
  | 0, hn, _ =>
    by
    let :
      Subsingleton
        (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point ⟨0, hn⟩) } 2) :=
      by
      obtain ⟨D⟩ := S.nonempty_firstSublevelDisk hf hn
      exact D.homology_subsingleton 2 (by norm_num)
    exact LinearEquiv.ofSubsingleton _ _
  | n + 1, hn, hpre =>
    Classical.choose
      (S.indexTwoBasis_step hf n hn hpre
        (indexTwoBasis (S := S) hf n (Nat.lt_of_succ_lt hn)
          (S.indexTwoPrefix_mono (Nat.le_succ n) hpre)))

def ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2 :=
  d.coreBoundaryHomologyMap 2 ((d.indexThreeBoundaryEquiv hindex).symm 1)

theorem ManifoldMorse.MorseSurgeryData.coreBoundary_two_eq_smul {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    (a :
      SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        2) :
    d.coreBoundaryHomologyMap 2 a =
      (d.indexThreeBoundaryEquiv hindex a) • d.indexThreeAttachingClass hindex := by
  conv_lhs => rw [d.indexThreeBoundary_scalar hindex a]
  rw [map_zsmul]
  rfl

theorem ManifoldMorse.MorseSurgeryData.coreBoundary_two_range {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    LinearMap.range (d.coreBoundaryHomologyMap 2) =
      Submodule.span ℤ {d.indexThreeAttachingClass hindex} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    rw [d.coreBoundary_two_eq_smul hindex b]
    exact
      Submodule.mem_span_singleton.mpr
        ⟨d.indexThreeBoundaryEquiv hindex b,
          int_smul_eq_zsmul
            (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 }
                2).isModule
            _ _⟩
  · intro ha
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp ha
    refine ⟨z • (d.indexThreeBoundaryEquiv hindex).symm 1, ?_⟩
    rw [map_zsmul]
    exact
      (int_smul_eq_zsmul
            (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 }
                2).isModule
            z (d.indexThreeAttachingClass hindex)).symm.trans
        hz

theorem ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_surjective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    Function.Surjective (d.lowerRealizationHomologyMap 2) := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        1) :=
    d.attachingHomology_subsingleton_of_index 1 one_ne_zero (by omega) (by omega)
  intro a
  have ha : a ∈ LinearMap.ker (d.morseConnectingMap hf 1) := Subsingleton.elim _ _
  rw [← d.morse_exact_at_upper hf 1] at ha
  exact ha

theorem ManifoldMorse.MorseSurgeryData.indexThree_lowerRealization_kernel {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) [T2Space M] (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    LinearMap.ker (d.lowerRealizationHomologyMap 2) =
      Submodule.span ℤ {d.indexThreeAttachingClass hindex} := by
  rw [← d.morse_exact_at_lower hf 2 (by norm_num), d.coreBoundary_two_range hindex]

def ManifoldMorse.MorseSurgeryData.indexThreePresentation {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) {r c : ℕ}
    (P :
      IntegerPresentation
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2) r c) :
    IntegerPresentation
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 2) r
      (c + 1) :=
  P.adjoin (d.lowerRealizationHomologyMap 2) (d.indexThree_lowerRealization_surjective hf hindex)
    (d.indexThreeAttachingClass hindex) (d.indexThree_lowerRealization_kernel hf hindex)

def ManifoldMorse.SurgeryWindows.middlePresentation {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r : ℕ)
    (htwo : S.HasIndexTwoPrefix r) :
    (c : ℕ) →
      (hc : r + c < S.count) →
        S.HasIndexThreeBlock r c →
          IntegerPresentation
            (SingularMayerVietoris.SingularHomology
              { x : M // f x ≤ S.upper (S.point ⟨r + c, hc⟩) } 2)
            r c
  | 0, hc, _ => IntegerPresentation.ofEquiv (S.indexTwoBasis hf r hc htwo)
  | c + 1, hc, hthree =>
    let P :=
      middlePresentation (S := S) hf r htwo c (Nat.lt_of_succ_lt hc)
        (S.indexThreeBlock_mono (Nat.le_succ c) hthree)
    let B := S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩ ⟨r + (c + 1), hc⟩ rfl
    (S.data (S.point ⟨r + (c + 1), hc⟩)).indexThreePresentation hf.continuous
      (S.indexThreeBlock_last r c hc hthree) (P.transport (B.homologyEquiv 2))

def ManifoldMorse.SurgeryWindows.middleMatrix {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c) :
    Matrix (Fin r) (Fin c) ℤ :=
  (S.middlePresentation hf r htwo c hc hthree).matrix

end
