/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Morse.CircleGluing
import Lib.Geometry.Manifold.Whitney.CleanStrips.CrossingChart
import Lib.Geometry.Manifold.Whitney.CleanStrips.SphereNormal

/-!
# Intersection numbers with the belt sphere of a Morse surgery

For a Morse surgery `d : ManifoldMorse.MorseSurgeryData E f p` and a smooth sphere
`g : Sᵐ → d.UpperLevel` in the upper level set, transverse to the belt sphere, of complementary
dimension:

* `beltIntersectionJacobian` and `beltIntersectionSign` are the local intersection number of `g`
  with the belt sphere at a parameter `x`, the sign of the normal Jacobian of
  `SphereNormalCoordinates`; it is `±1` at every intersection point
  (`beltIntersectionSign_unit`);
* `finite_beltIntersectionPoints` : an injective such `g` meets the belt sphere in finitely many
  points, as two compact submanifolds of complementary dimension meeting transversally;
* `beltIntersectionCount` is the algebraic intersection number, the sum of the local signs.

## References

* [John Milnor, *Lectures on the h-cobordism theorem*][milnor65], §6 (intersection numbers of the
  attaching and belt spheres).
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace

noncomputable section

/-- A reference linear isomorphism between the radial line times the negative coordinates of the
Morse chart and the ambient space of the belt sphere, available once the negative coordinates
have dimension `m`.
-/
def ManifoldMorse.MorseSurgeryData.beltNormalReference {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m) :
    (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, hdim, Nat.add_comm])

/-- The normal Jacobian at `x` of a sphere `g` meeting the belt sphere of a Morse surgery, computed
from the derivative of the belt normal coordinate of `g`.
-/
def ManifoldMorse.MorseSurgeryData.beltIntersectionJacobian {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m) : ℝ :=
  letI : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  SphereNormalCoordinates.normalJacobian j x
    (mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x)

/-- The local intersection sign at `x` of a sphere with the belt sphere of a Morse surgery, the sign
of the corresponding normal Jacobian (Milnor, h-cobordism theorem, §6).
-/
def ManifoldMorse.MorseSurgeryData.beltIntersectionSign {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m) : SignType :=
  SignType.sign (d.beltIntersectionJacobian m j g x)

/-- The set of parameters at which a sphere `g` meets the belt sphere of a Morse surgery. -/
def ManifoldMorse.MorseSurgeryData.beltIntersectionPoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : Hemisphere.Sphere m → d.UpperLevel) : Set (Hemisphere.Sphere m) :=
  g ⁻¹' Set.range d.surgery.beltSphere

/-- Two intersection points carry opposite signs exactly when the product of their normal Jacobians
is negative.
-/
theorem ManifoldMorse.MorseSurgeryData.beltIntersectionSigns_opposite_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) (x y : Hemisphere.Sphere m) :
    d.beltIntersectionSign m j g x * d.beltIntersectionSign m j g y = -1 ↔
      d.beltIntersectionJacobian m j g x * d.beltIntersectionJacobian m j g y < 0 := by
  unfold beltIntersectionSign
  rw [← sign_mul, sign_eq_neg_one_iff]

/-- The algebraic intersection number of a sphere with the belt sphere of a Morse surgery: the sum
of the local signs over the finitely many intersection points.
-/
def ManifoldMorse.MorseSurgeryData.beltIntersectionCount {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel)
    (hfin : (d.beltIntersectionPoints m g).Finite) : ℤ :=
  ∑ x ∈ hfin.toFinset, (d.beltIntersectionSign m j g x : ℤ)

attribute [local instance 100] Classical.propDecidable in
/-- At a transverse intersection point with the belt sphere the normal Jacobian is nonzero. -/
theorem ManifoldMorse.MorseSurgeryData.beltIntersectionJacobian_ne_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g → d.beltIntersectionJacobian m j g x ≠ 0 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient (m + 1)) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hA := d.bijective_beltNormal_comp_of_transverse hf n m hdim g hg x v hv (ht x v hv)
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] d.chart.NegativeCoordinates :=
    mfderiv (𝓡 m) 𝓘(ℝ, d.chart.NegativeCoordinates) (d.beltNormal ∘ g) x
  have hAi : A.IsInvertible :=
    ⟨(LinearEquiv.ofBijective A.toLinearMap hA).toContinuousLinearEquiv, rfl⟩
  exact SphereNormalCoordinates.normalJacobian_ne_zero j x A hAi

attribute [local instance 100] Classical.propDecidable in
/-- At a transverse intersection point with the belt sphere the local sign is `1` or `-1`. -/
theorem ManifoldMorse.MorseSurgeryData.beltIntersectionSign_unit {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (n m : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient (m + 1))
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m),
      x ∈ d.beltIntersectionPoints m g →
        d.beltIntersectionSign m j g x = 1 ∨ d.beltIntersectionSign m j g x = -1 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht x hx
  have hn : d.beltIntersectionSign m j g x ≠ 0 :=
    sign_ne_zero.mpr (d.beltIntersectionJacobian_ne_zero hf n m hdim j g hg ht x hx)
  rcases SignType.trichotomy (d.beltIntersectionSign m j g x) with h | h | h
  · exact Or.inr h
  · exact (hn h).elim
  · exact Or.inl h

attribute [local instance 100] Classical.propDecidable in
/-- An injective sphere meeting the belt sphere transversally does so in finitely many points, the
two being compact submanifolds of complementary dimension in the upper level set.
-/
theorem ManifoldMorse.MorseSurgeryData.finite_beltIntersectionPoints {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    [T2Space M] [CompactSpace M] (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) g
            d.surgery.beltSphere x y),
      (d.beltIntersectionPoints m g).Finite := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro hg hinj ht
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) =
      Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace_fin]
    have hp : Module.finrank ℝ d.chart.PositiveCoordinates = n + 1 := Fact.out
    have hs := d.chart.finrank_negative_add_positive
    omega
  have hfin :=
    finite_transverse_intersections hg (d.belt_smooth hf n) hinj
      d.belt_isClosedEmbedding.injective hdim' (fun x y hxy => ht x y hxy)
  have hpre : (g ⁻¹' (Set.range g ∩ Set.range d.surgery.beltSphere)).Finite :=
    hfin.preimage hinj.injOn
  exact hpre.subset (fun x hx => ⟨⟨x, rfl⟩, hx⟩)

end
