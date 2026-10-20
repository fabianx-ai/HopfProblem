/-
Copyright (c) 2026 Fabian Franz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabian Franz
-/
module

public import Mathlib
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.Avoidance
public import Lib.Geometry.Manifold.Morse.SurgeryWindows.Hemisphere
public import Lib.AlgebraicTopology.SingularHomology.Sphere

/-!
# Maps into the complement of a compact smooth image

Let `g : Y → N` be a smooth map of a compact manifold with closed range, and `domain g` the open
complement of its range. If `dim X + 1 + dim Y < dim N`, two smooth maps `X → domain g` that are
homotopic in `N` are homotopic in `domain g`
(`ImageComplement.homotopic_of_ambient_homotopic`): smooth the ambient homotopy rel collars and
push it off the image of `g` by general position
(`Lib.Geometry.Manifold.Morse.SurgeryWindows.Avoidance`). In particular, if every loop in `N`
is nullhomotopic and `2 + dim Y < dim N`, every loop in the complement is nullhomotopic
(`ImageComplement.circle_nullhomotopies`). Cf. Hirsch, *Differential Topology*, Ch. 3.
-/

open Set Function Filter Manifold Topology

open scoped ContDiff ENNReal

@[expose] public noncomputable section

/-- The open complement of a compact image. -/
def ImageComplement.domain {Y N : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace N] [T2Space N] (g : C(Y, N)) : TopologicalSpace.Opens N :=
  ⟨(Set.range g)ᶜ, (isCompact_range g.continuous).isClosed.isOpen_compl⟩

/-- The inclusion of the image complement. -/
def ImageComplement.inclusion {Y N : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace N] [T2Space N] (g : C(Y, N)) : C(domain g, N) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- An ambient homotopy off the image gives a smooth homotopy in the complement. -/
theorem ImageComplement.exists_smooth_homotopy_of_ambient_homotopic {Y N : Type*}
    [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace N] [T2Space N]
    {E E' G H H' K X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace K] {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
    {J : ModelWithCorners ℝ G K} [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X]
    [IsManifold I ∞ X] [T2Space X] [CompactSpace X] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [ChartedSpace K N] [IsManifold J ∞ N] (g : C(Y, N)) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + 1 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (f₀ f₁ : C(X, domain g)) (hf₀ : ContMDiff I J ∞ f₀) (hf₁ : ContMDiff I J ∞ f₁)
    (hambient :
      ((ImageComplement.inclusion g).comp f₀).Homotopic
        ((ImageComplement.inclusion g).comp f₁)) :
    ∃ H : f₀.Homotopy f₁,
      ContMDiff ((𝓡∂ 1).prod I) J ∞ H ∧
        (∀ t : unitInterval, ∀ x, (t : ℝ) ≤ 1 / 4 → H (t, x) = f₀ x) ∧
          (∀ t : unitInterval, ∀ x, 3 / 4 ≤ (t : ℝ) → H (t, x) = f₁ x) := by
  obtain ⟨H⟩ := hambient
  have hval : ContMDiff J J ∞ (ImageComplement.inclusion g) := contMDiff_subtype_val
  have hf₀val : ContMDiff I J ∞ ((ImageComplement.inclusion g).comp f₀) := hval.comp hf₀
  have hf₁val : ContMDiff I J ∞ ((ImageComplement.inclusion g).comp f₁) := hval.comp hf₁
  obtain ⟨H, hH, hlo, hhi⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars hf₀val hf₁val H
  have hd :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × E) + Module.finrank ℝ E' < Module.finrank ℝ G := by
    simp only [Module.finrank_prod, finrank_euclideanSpace_fin]
    omega
  have hfixed : ∀ q ∈ ManifoldSmoothing.homotopyCollars X, H q ∉ Set.range g := by
    rintro ⟨t, x⟩ (ht | ht)
    · rw [hlo t x ht]
      exact (f₀ x).property
    · rw [hhi t x ht]
      exact (f₁ x).property
  obtain ⟨F, hF, hrel, hdisjoint⟩ :=
    GeneralPosition.exists_disjoint_smooth_map_homotopicRel H.toContinuousMap g hH hg hd
      ManifoldSmoothing.isClosed_homotopyCollars hfixed
  have heq : Set.EqOn F H (ManifoldSmoothing.homotopyCollars X) := fun _ hq =>
    (hrel.fst_eq_snd hq).symm
  have havoid : ∀ q, F q ∈ domain g := by
    intro q
    change F q ∉ Set.range g
    exact fun hq => Set.disjoint_left.mp hdisjoint ⟨q, rfl⟩ hq
  let A : C(unitInterval × X, domain g) := ⟨fun q => ⟨F q, havoid q⟩, F.continuous.subtype_mk _⟩
  have hA : ContMDiff ((𝓡∂ 1).prod I) J ∞ A := (ContMDiff.subtypeVal_comp_iff (domain g) A).mp hF
  have hAlo (t : unitInterval) (x : X) (ht : (t : ℝ) ≤ 1 / 4) : A (t, x) = f₀ x := by
    apply Subtype.ext
    exact
      (heq (show (t, x) ∈ ManifoldSmoothing.homotopyCollars X from Or.inl ht)).trans
        (hlo t x ht)
  have hAhi (t : unitInterval) (x : X) (ht : 3 / 4 ≤ (t : ℝ)) : A (t, x) = f₁ x := by
    apply Subtype.ext
    exact
      (heq (show (t, x) ∈ ManifoldSmoothing.homotopyCollars X from Or.inr ht)).trans
        (hhi t x ht)
  exact
    ⟨{  toContinuousMap := A
        map_zero_left := fun x => hAlo 0 x (by norm_num)
        map_one_left := fun x => hAhi 1 x (by norm_num) }, hA, hAlo, hAhi⟩

/-- Maps ambiently homotopic off the image are homotopic in the complement. -/
theorem ImageComplement.homotopic_of_ambient_homotopic {Y N : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [TopologicalSpace N] [T2Space N] {E E' G H H' K X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
    [CompactSpace X] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [ChartedSpace K N] [IsManifold J ∞ N]
    (g : C(Y, N)) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + 1 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (f₀ f₁ : C(X, domain g))
    (hambient :
      ((ImageComplement.inclusion g).comp f₀).Homotopic
        ((ImageComplement.inclusion g).comp f₁)) :
    f₀.Homotopic f₁ := by
  obtain ⟨f₀', hf₀', h₀⟩ :=
    ManifoldSmoothing.exists_smooth_map_homotopic (I := I) (J := J) f₀
  obtain ⟨f₁', hf₁', h₁⟩ :=
    ManifoldSmoothing.exists_smooth_map_homotopic (I := I) (J := J) f₁
  have ha₀ := (ContinuousMap.Homotopic.refl (ImageComplement.inclusion g)).comp h₀
  have ha₁ := (ContinuousMap.Homotopic.refl (ImageComplement.inclusion g)).comp h₁
  obtain ⟨H, -⟩ :=
    exists_smooth_homotopy_of_ambient_homotopic g hg hdim f₀' f₁' hf₀' hf₁'
      (ha₀.symm.trans (hambient.trans ha₁))
  exact h₀.trans ((show f₀'.Homotopic f₁' from ⟨H⟩).trans h₁.symm)

/-- An ambiently nullhomotopic map missing the image is nullhomotopic in the complement. -/
theorem ImageComplement.nullhomotopic_of_ambient_nullhomotopic {E E' G H H' K X Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
    {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K}
    [J.Boundaryless] [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
    [CompactSpace X] [Nonempty X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
    [CompactSpace Y] [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]
    (g : C(Y, N)) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + 1 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (f : C(X, domain g))
    (hambient :
      ∃ c, ((ImageComplement.inclusion g).comp f).Homotopic (ContinuousMap.const X c)) :
    ∃ c, f.Homotopic (ContinuousMap.const X c) := by
  classical
  obtain ⟨c, hc⟩ := hambient
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  have hconst :
    (ContinuousMap.const X ((f x₀ : domain g) : N)).Homotopic (ContinuousMap.const X c) :=
    hc.comp (ContinuousMap.Homotopic.refl (ContinuousMap.const X x₀))
  refine
    ⟨f x₀, homotopic_of_ambient_homotopic (I := I) g hg hdim f (ContinuousMap.const X (f x₀)) ?_⟩
  exact hc.trans hconst.symm

/-- Let `Y` be a compact smooth manifold, `N` a boundaryless Hausdorff smooth manifold and
  `g : Y → N` smooth. If every loop in `N` is nullhomotopic and `2 + dim Y < dim N`, every loop in
  the complement of the range of `g` is nullhomotopic. -/
theorem ImageComplement.circle_nullhomotopies {E' G H' K Y N : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H'] [TopologicalSpace K]
    {I' : ModelWithCorners ℝ E' H'} {J : ModelWithCorners ℝ G K} [J.Boundaryless]
    [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
    [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N] (g : C(Y, N))
    (hg : ContMDiff I' J ∞ g) (hdim : 2 + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hnull : ∀ f : C(Hemisphere.Sphere 1, N), ∃ c, f.Homotopic (ContinuousMap.const _ c)) :
    ∀ f : C(Hemisphere.Sphere 1, domain g), ∃ c, f.Homotopic (ContinuousMap.const _ c) := by
  let : Nonempty (Hemisphere.Sphere 1) := NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  intro f
  apply nullhomotopic_of_ambient_nullhomotopic (I := 𝓡 1) g hg _ f (hnull _)
  simpa only [finrank_euclideanSpace_fin] using hdim

