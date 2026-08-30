/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Lib.Topology.Gluing.OverBase
public import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Manifold structures on spaces glued over a covered base

A glued space inherits a `C^n` manifold structure when its pieces are `C^n` manifolds and all
piece transitions are `C^n`.  For a star cover it suffices to check each central overlap and its
inverse.
-/

@[expose] public section

open Set Function Filter Manifold Topology
open Mathoverflow1973
open scoped ContDiff Manifold Topology

noncomputable section

universe u

namespace Mathoverflow1973

@[simp]
theorem ThreefoldGluing.Data.parametrization_symm_inclusion {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] (i : D.J) (x : D.piece i) :
    (D.parametrization i).symm (D.inclusion i x) = x :=
  (D.parametrization i).left_inv (Set.mem_univ x)

def ThreefoldGluing.Data.gluedChart {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] (i : D.J) (x : D.piece i) :
    OpenPartialHomeomorph D.Space E :=
  (D.parametrization i).symm.trans (chartAt E x)

theorem ThreefoldGluing.Data.gluedChart_symm {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] (i : D.J) (x : D.piece i) :
    ((D.gluedChart i x).symm : E → D.Space) = D.inclusion i ∘ (chartAt E x).symm := by
  funext z
  rfl

@[simp]
theorem ThreefoldGluing.Data.gluedChart_inclusion {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] (i : D.J) (x y : D.piece i) :
    D.gluedChart i x (D.inclusion i y) = chartAt E x y := by
  change chartAt E x ((D.parametrization i).symm (D.inclusion i y)) = _
  rw [parametrization_symm_inclusion]

theorem ThreefoldGluing.Data.gluedChart_inclusion_mem_source {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] (i : D.J) (x : D.piece i) :
    D.inclusion i x ∈ (D.gluedChart (E := E) i x).source := by
  change
    D.inclusion i x ∈ (D.parametrization i).target ∧
      (D.parametrization i).symm (D.inclusion i x) ∈ (chartAt E x).source
  rw [parametrization_target, parametrization_symm_inclusion]
  exact ⟨Set.mem_range_self x, mem_chart_source E x⟩

@[instance_reducible]
def ThreefoldGluing.Data.chartedSpace {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] : ChartedSpace E D.Space
    where
  atlas := Set.range (fun r : Σ i, D.piece i => D.gluedChart (E := E) r.1 r.2)
  chartAt x := D.gluedChart (D.representative x).1 (D.representative x).2
  mem_chart_source
    x := by
    simpa only [inclusion_representative] using
      D.gluedChart_inclusion_mem_source (E := E) (D.representative x).1 (D.representative x).2
  chart_mem_atlas x := Set.mem_range_self (D.representative x)

theorem ThreefoldGluing.Data.gluedChart_mem_atlas {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] (i : D.J) (x : D.piece i) :
    letI := D.chartedSpace (E := E)
    D.gluedChart i x ∈ atlas E D.Space :=
  Set.mem_range_self (⟨i, x⟩ : Σ i, D.piece i)

theorem ThreefoldGluing.Data.gluedChart_transition_apply {B : Type u} [TopologicalSpace B]
    (D : ThreefoldGluing.Data B) [∀ i, Nonempty (D.piece i)] {E : Type*} [NormedAddCommGroup E]
    [∀ i, ChartedSpace E (D.piece i)] (i j : D.J) (x : D.piece i) (y : D.piece j) {z : E}
    (hz : z ∈ ((D.gluedChart (E := E) i x).symm.trans (D.gluedChart (E := E) j y)).source) :
    ((D.gluedChart (E := E) i x).symm.trans (D.gluedChart (E := E) j y)) z =
      chartAt E y (D.transition i j ((chartAt E x).symm z)) := by
  have hinc : D.inclusion i ((chartAt E x).symm z) ∈ (D.gluedChart (E := E) j y).source := hz.2
  have hrange : D.inclusion i ((chartAt E x).symm z) ∈ Set.range (D.inclusion j) := by
    simpa only [OpenPartialHomeomorph.symm_symm, parametrization_target] using hinc.1
  have he := (D.parametrization_transition i j hrange).2
  change chartAt E y ((D.parametrization j).symm (D.inclusion i ((chartAt E x).symm z))) = _
  rw [he]

end Mathoverflow1973

/-- Coordinate changes between glued charts inherit the differentiability of the underlying
piece transition. -/
theorem Mathoverflow1973.ThreefoldGluing.Data.gluedChart_transition_contMDiff
    {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    [∀ i, Nonempty (D.piece i)]
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [∀ i, ChartedSpace E (D.piece i)]
    {n : ℕ∞ω}
    [∀ i, IsManifold 𝓘(𝕜, E) n (D.piece i)]
    (htr : ∀ i j, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n (D.transition i j)
      (D.transition i j).source)
    (i j : D.J) (x : D.piece i) (y : D.piece j) :
    ContDiffOn 𝕜 n ((D.gluedChart (E := E) i x).symm.trans (D.gluedChart (E := E) j y))
      ((D.gluedChart (E := E) i x).symm.trans (D.gluedChart (E := E) j y)).source := by
  intro z hz
  have hza : z ∈ (chartAt E x).target := hz.1.1
  have hinc : D.inclusion i ((chartAt E x).symm z) ∈
      (D.gluedChart (E := E) j y).source := hz.2
  have hrange : D.inclusion i ((chartAt E x).symm z) ∈ Set.range (D.inclusion j) := by
    simpa only [OpenPartialHomeomorph.symm_symm,
      ThreefoldGluing.Data.parametrization_target] using hinc.1
  obtain ⟨htransition, he⟩ := D.parametrization_transition i j hrange
  have ha := (chartAt E x).map_target hza
  have hb : D.transition i j ((chartAt E x).symm z) ∈ (chartAt E y).source := by
    rw [← he]
    exact hinc.2
  have hmid := (htr i j).contMDiffAt ((D.transition i j).open_source.mem_nhds htransition)
  have hc := ((contMDiffAt_iff_of_mem_source ha hb).mp hmid).2
  have hc' : ContDiffAt 𝕜 n (chartAt E y ∘ D.transition i j ∘ (chartAt E x).symm) z := by
    simpa [extChartAt, OpenPartialHomeomorph.extend, contDiffWithinAt_univ,
      (chartAt E x).right_inv hza] using hc
  apply hc'.contDiffWithinAt.congr_of_mem ?_ hz
  intro w hw
  exact D.gluedChart_transition_apply i j x y hw

/-- A glued charted space is a manifold when every piece is a manifold and every transition is
`C^n` over the chosen scalar field. -/
theorem Mathoverflow1973.ThreefoldGluing.Data.isManifold_of_contMDiffOn_transition
    {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    [∀ i, Nonempty (D.piece i)]
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [∀ i, ChartedSpace E (D.piece i)]
    {n : ℕ∞ω}
    [∀ i, IsManifold 𝓘(𝕜, E) n (D.piece i)]
    (htr : ∀ i j, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n (D.transition i j)
      (D.transition i j).source) :
    letI := D.chartedSpace (E := E)
    IsManifold 𝓘(𝕜, E) n D.Space := by
  let _ := D.chartedSpace (E := E)
  apply isManifold_of_contDiffOn
  rintro e e' ⟨⟨i, x⟩, rfl⟩ ⟨⟨j, y⟩, rfl⟩
  simpa using D.gluedChart_transition_contMDiff htr i j x y

/-- The transition system of a star is `C^n` when every overlap and inverse overlap is `C^n`. -/
theorem Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.transition_contMDiff
    {B I : Type u} [TopologicalSpace B]
    (D : SpecialPeriods.Threefold.Star.Input B I)
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [∀ i, ChartedSpace E (D.piece i)] {n : ℕ∞ω}
    (htr : ∀ i, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n (D.overlap i) (D.overlap i).source)
    (hinv : ∀ i, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n (D.overlap i).symm
      (D.overlap i).target)
    (i j : Option I) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n (D.transition i j) (D.transition i j).source := by
  cases i with
  | none =>
      cases j with
      | none =>
          rw [D.transition_none_none]
          change ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n
            (id : D.piece Option.none → D.piece Option.none) Set.univ
          exact contMDiffOn_id
      | some j =>
          rw [D.transition_none_some]
          simpa only [OpenPartialHomeomorph.symm_source] using hinv j
  | some i =>
      cases j with
      | none =>
          rw [D.transition_some_none]
          exact htr i
      | some j =>
          by_cases h : i = j
          · subst j
            rw [D.transition_some_self]
            change ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n
              (id : D.piece (Option.some i) → D.piece (Option.some i)) Set.univ
            exact contMDiffOn_id
          · rw [D.transition_some_some_source_eq_empty h]
            exact contMDiffOn_empty

/-- `Star.Input.transition_contMDiff` for the associated generic gluing data. -/
theorem Mathoverflow1973.SpecialPeriods.Threefold.Star.Input.toData_transition_contMDiff
    {B I : Type u} [TopologicalSpace B]
    (D : SpecialPeriods.Threefold.Star.Input B I)
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [∀ i, ChartedSpace E (D.piece i)] {n : ℕ∞ω}
    (htr : ∀ i, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n (D.overlap i) (D.overlap i).source)
    (hinv : ∀ i, ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n (D.overlap i).symm
      (D.overlap i).target)
    (i j : D.toData.J) :
    ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n (D.toData.transition i j)
      (D.toData.transition i j).source := by
  change ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E) n (D.transition i j) (D.transition i j).source
  exact D.transition_contMDiff htr hinv i j
