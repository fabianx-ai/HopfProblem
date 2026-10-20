/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/

import Mathlib
import Lib.Geometry.Manifold.Whitney.FrameField.RankThreeCorners
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.SphereNormalCoordinates
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.WhitneyDisc
import Lib.Geometry.Manifold.Whitney.EmbeddedArcs.StripPair

/-!
# Whitney bigons against a belt sphere in dimension six

The specialisation used for a Morse surgery of index two in a six-manifold
(`Module.finrank ℝ E = 6`, `Module.finrank ℝ D.chart.NegativeCoordinates = 2`), with a two-sphere
`g : Hemisphere.Sphere 2 → D.UpperLevel` meeting the belt sphere:

* the two belt intersection signs of `g` are opposite exactly when the two corner determinants of
  the Whitney bigon between `g` and the belt sphere are
  (`ManifoldMorse.MorseSurgeryData.opposite_beltIntersectionSigns_iff_Whitney_corners`);
* in a compact manifold whose lower level has null-homotopic circles, a clean bigon boundary
  between `g` and the belt sphere bounds a tubular bigon of codimension three
  (`ManifoldMorse.MorseSurgeryData.nonempty_belt_tubularBigon`), and its two arcs carry a clean
  strip pair with strip normal data of ranks one and two
  (`ManifoldMorse.MorseSurgeryData.exists_belt_tubular_strip_pair`).

These three statements fix the dimensions of one application of the Whitney trick (Milnor,
*Lectures on the h-cobordism theorem*, §6, with `n = 6`); they are kept in the library because
`Morse/BeltCancellation` uses them.

## Tags

Whitney trick, belt sphere, Morse surgery
-/

open Set Function Filter Manifold Topology

open scoped ContDiff InnerProductSpace NNReal

noncomputable section

attribute [local instance 100] Classical.propDecidable in
/-- For a Morse surgery in a six-manifold with a two-dimensional index, the two belt intersection
signs of an embedded two-sphere are opposite exactly when the two corner determinants of the
Whitney bigon between the sphere and the belt sphere are. -/
theorem ManifoldMorse.MorseSurgeryData.opposite_beltIntersectionSigns_iff_Whitney_corners
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : Hemisphere.Sphere 2 → D.UpperLevel) {a b : ℝ → D.UpperLevel}
    {k l : (ℝ × ℝ) → D.UpperLevel} {h : ℝ} :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x))
      (_ht :
        ∀ x y,
          NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) g
            D.surgery.beltSphere x y)
      (tube :
        TubularBigon (E := RegularLevel.Model E) (Set.range g)
          (Set.range D.surgery.beltSphere) a b k l h 3)
      (d :
        StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E :=
          RegularLevel.Model E) (Set.range g) k)
      (e :
        StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E :=
          RegularLevel.Model E) (Set.range D.surgery.beltSphere) l)
      (x₀ x₁ : Hemisphere.Sphere 2),
      g x₀ = d.chart (StripCoordinates.center 0) →
        g x₁ = d.chart (StripCoordinates.center 1) →
          ((D.beltIntersectionSign 2 r g x₀ * D.beltIntersectionSign 2 r g x₁ = -1) ↔
            tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg hinj hi ht tube d e x₀ x₁ hx₀ hx₁
  let j : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] D.chart.NegativeCoordinates :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod, hindex])
  let q := D.beltSheetNormal j
  let r' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) j).trans r
  have hjSmooth :
    ContMDiff 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ j.symm :=
    j.symm.contDiff.contMDiff
  have hdata (x : Hemisphere.Sphere 2) (hx : g x ∈ Set.range D.surgery.beltSphere) :
    ContMDiffAt 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q (g x) ∧
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (q ∘ g) x).IsInvertible ∧
        SphereNormalCoordinates.normalJacobian r' x
            (mfderiv (𝓡 2) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (q ∘ g) x) =
          D.beltIntersectionJacobian 2 r g x := by
    obtain ⟨v, hv⟩ := hx
    have hxO : g x ∈ D.beltNormalDomain := hv ▸ D.belt_mem_normalDomain v
    have hnormal :=
      (D.contMDiffOn_beltNormal hf).contMDiffAt (D.isOpen_beltNormalDomain.mem_nhds hxO)
    have hq :
      ContMDiffAt 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q (g x) :=
      hjSmooth.contMDiffAt.comp _ hnormal
    let A : EuclideanSpace ℝ (Fin 2) →L[ℝ] D.chart.NegativeCoordinates :=
      mfderiv (𝓡 2) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g) x
    let B : EuclideanSpace ℝ (Fin 2) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) :=
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (q ∘ g) x
    have hAb : Function.Bijective A :=
      D.bijective_beltNormal_comp_of_transverse hf 3 2 hindex g hg x v hv (ht x v hv)
    have hA : A.IsInvertible :=
      ⟨(LinearEquiv.ofBijective A.toLinearMap hAb).toContinuousLinearEquiv, rfl⟩
    have hJ :
      mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) j.symm
          (D.beltNormal (g x)) =
        j.symm.toContinuousLinearMap := by
      rw [mfderiv_eq_fderiv]
      exact j.symm.toContinuousLinearMap.fderiv
    have hBA : B = j.symm.toContinuousLinearMap.comp A := by
      change mfderiv (𝓡 2) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) (j.symm ∘ (D.beltNormal ∘ g)) x = _
      rw [mfderiv_comp x (hjSmooth.mdifferentiableAt (by simp))
          ((hnormal.comp x hg.contMDiffAt).mdifferentiableAt (by simp))]
      change
        (mfderiv 𝓘(ℝ, D.chart.NegativeCoordinates) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) j.symm
                  (D.beltNormal (g x)) :
                D.chart.NegativeCoordinates →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1))).comp
            A =
          _
      exact
        congrArg
          (fun L : D.chart.NegativeCoordinates →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) => L.comp A)
          hJ
    refine ⟨hq, ?_, ?_⟩
    · change B.IsInvertible
      rw [hBA]
      exact (show j.symm.toContinuousLinearMap.IsInvertible from ⟨j.symm, rfl⟩).comp hA
    · change
        SphereNormalCoordinates.normalJacobian r' x B =
          SphereNormalCoordinates.normalJacobian r x A
      rw [hBA]
      exact SphereNormalCoordinates.normalJacobian_change_normal_model r j x A hA
  have hcross (t : ℝ) (ht' : t = 0 ∨ t = 1) (x : Hemisphere.Sphere 2)
    (hx : g x = d.chart (StripCoordinates.center t)) :
    g x ∈ Set.range D.surgery.beltSphere := by
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by rcases ht' with rfl | rfl <;> simp
    rw [hx, tube.rankThree_corner_sheet_charts_coincide d e ht']
    exact (e.sheet _ (e.line htI)).mpr rfl
  obtain ⟨hq₀, hi₀, hJ₀⟩ := hdata x₀ (hcross 0 (Or.inl rfl) x₀ hx₀)
  obtain ⟨hq₁, hi₁, hJ₁⟩ := hdata x₁ (hcross 1 (Or.inr rfl) x₁ hx₁)
  have hsign :=
    SphereNormalCoordinates.opposite_normalJacobians_iff_retained_sheet d.chart g hg hinj hi
      d.sheet d.line (by simp [Module.finrank_prod]) q r' x₀ x₁ hx₀ hx₁ hq₀ hq₁ hi₀ hi₁
  rw [hJ₀, hJ₁] at hsign
  exact
    (D.beltIntersectionSigns_opposite_iff 2 r g x₀ x₁).trans
      (hsign.trans (D.opposite_belt_corners_iff_normal_sheet_determinants hf j tube d e).symm)


attribute [local instance 100] Classical.propDecidable in
/-- In a compact six-manifold (`[CompactSpace M]`) with a Morse surgery of index two whose lower
level has null-homotopic circles (`hnull`), a clean bigon boundary between a smooth two-sphere
`g` in the upper level and the belt sphere bounds a tubular bigon of codimension three. No
injectivity or immersion hypothesis on `g` is assumed. -/
theorem ManifoldMorse.MorseSurgeryData.nonempty_belt_tubularBigon {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, d.LowerLevel),
        ∃ q, g.Homotopic (ContinuousMap.const _ q))
    (g : C(Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g) {a b : ℝ → d.UpperLevel}
      {k l : (ℝ × ℝ) → d.UpperLevel} {h : ℝ},
      CleanBigonBoundary (E := RegularLevel.Model E) (Set.range g)
          (Set.range d.surgery.beltSphere) a b k l h →
        Nonempty
          (TubularBigon (E := RegularLevel.Model E) (Set.range g)
            (Set.range d.surgery.beltSphere) a b k l h 3) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro hg a b k l h B
  have hT : IsClosed (Set.range d.surgery.beltSphere) := d.belt_isClosedEmbedding.isClosed_range
  have hnullbelt :=
    d.chart.surgery_beltComplement_circle_nullhomotopies hf d.radius d.radius_pos d.block
      d.lower_regular d.surgery d.oldPiece_eq hindex (by omega) hnull
  exact
    B.nonempty_tubularBigon_of_complement_contractions g hg hT hnullbelt
      (by simp [RegularLevel.Model, hdim]) (by simp [RegularLevel.Model, hdim]) 3
      (by simp [RegularLevel.Model, hdim])

attribute [local instance 100] Classical.propDecidable in
/-- In the same situation, the two arcs of the bigon boundary carry a clean strip pair with strip
normal data of ranks one and two, which is the input of the rank-three Whitney model. -/
theorem ManifoldMorse.MorseSurgeryData.exists_belt_tubular_strip_pair {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ g : C(Hemisphere.Sphere 1, d.LowerLevel),
        ∃ q, g.Homotopic (ContinuousMap.const _ q))
    (g : C(Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := d.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x))
      (_ht :
        ∀ x y,
          d.surgery.beltSphere y = g x →
            Function.Surjective
              ((mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x).coprod
                (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) d.surgery.beltSphere y)))
      (x₀ x₁ : Hemisphere.Sphere 2)
      (y₀ y₁ : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates),
      d.surgery.beltSphere y₀ = g x₀ →
        d.surgery.beltSphere y₁ = g x₁ →
          x₀ ≠ x₁ →
            ∃ a b : ℝ → d.UpperLevel,
              a 0 = g x₀ ∧
                a 1 = g x₁ ∧
                  b 0 = g x₀ ∧
                    b 1 = g x₁ ∧
                      ∃ k₀ k₁ l₀ l₁ : (ℝ × ℝ) → d.UpperLevel,
                        ∃ k :
                          CleanStripPatch (E := RegularLevel.Model E) (Set.range g)
                            (Set.range d.surgery.beltSphere) a k₀ k₁,
                          ∃ l :
                            CleanStripPatch (E := RegularLevel.Model E)
                              (Set.range d.surgery.beltSphere) (Set.range g) b l₀ l₁,
                            Nonempty
                                (StripNormalData (EuclideanSpace ℝ (Fin 1))
                                  (EuclideanSpace ℝ (Fin 3)) (E := RegularLevel.Model E)
                                  (Set.range g) k.map) ∧
                              Nonempty
                                  (StripNormalData (EuclideanSpace ℝ (Fin 2))
                                    (EuclideanSpace ℝ (Fin 2)) (E := RegularLevel.Model E)
                                    (Set.range d.surgery.beltSphere) l.map) ∧
                                ∀ h : ℝ,
                                  0 < h →
                                    Nonempty
                                      (TubularBigon (E := RegularLevel.Model E)
                                        (Set.range g) (Set.range d.surgery.beltSphere) a b k.map
                                        l.map h 3) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  have hpos : Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1 := by
    have hh := d.chart.finrank_negative_add_positive
    omega
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) := ⟨hpos⟩
  intro hg hinj hi ht x₀ x₁ y₀ y₁ hcross₀ hcross₁ hxy
  have hpath₂ : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isPathConnected_sphere (by simp [← Module.finrank_eq_rank]) 0 (by norm_num)
  have hpath₃ : IsPathConnected (Metric.sphere (0 : d.chart.PositiveCoordinates) 1) :=
    isPathConnected_sphere (by rw [← Module.finrank_eq_rank, hpos]; norm_num) 0 (by norm_num)
  let γ : Path x₀ x₁ := (hpath₂.joinedIn x₀ x₀.property x₁ x₁.property).joined_subtype.somePath
  let η : Path y₀ y₁ := (hpath₃.joinedIn y₀ y₀.property y₁ y₁.property).joined_subtype.somePath
  have hG := d.belt_smooth hf 3
  have hiG := d.belt_derivative_injective hf 3
  obtain
    ⟨α, β, -, -, hα₀, hα₁, hβ₀, hβ₁, -, -, -, -, -, -, -, c₀, c₁, k, l, hnK, hnL, -, hboundary⟩ :=
    exists_shared_corner_strip_pair_of_two_le_finrank hg hG hinj
      d.belt_isClosedEmbedding.injective hi hiG (by simp) (by simp)
      (by simp [RegularLevel.Model, hdim]) ht hcross₀ hcross₁ hxy γ η
  refine
    ⟨g ∘ α, d.surgery.beltSphere ∘ β, ?_, ?_, ?_, ?_, c₀.map, c₁.map, c₀.swap.map, c₁.swap.map, k,
      l, ?_, ?_, ?_⟩
  · change g (α 0) = g x₀
    rw [hα₀]
  · change g (α 1) = g x₁
    rw [hα₁]
  · change d.surgery.beltSphere (β 0) = g x₀
    rw [hβ₀, hcross₀]
  · change d.surgery.beltSphere (β 1) = g x₁
    rw [hβ₁, hcross₁]
  · have transport (m n : ℕ) (hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) - 1 = m)
      (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = n) :
      Nonempty
        (StripNormalData (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)) (E :=
          RegularLevel.Model E) (Set.range g) k.map) := by
      subst m
      subst n
      exact hnK
    exact transport 1 3 (by simp) (by simp)
  · have transport (m n : ℕ) (hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1 = m)
      (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = n) :
      Nonempty
        (StripNormalData (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)) (E :=
          RegularLevel.Model E) (Set.range d.surgery.beltSphere) l.map) := by
      subst m
      subst n
      exact hnL
    exact transport 2 2 (by simp) (by simp)
  · intro h hh
    obtain ⟨B⟩ := hboundary h hh
    exact d.nonempty_belt_tubularBigon hf hdim hindex hnull g hg B

end
